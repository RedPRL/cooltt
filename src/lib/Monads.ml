module D = Domain
module S = Syntax
module St = ElabState
open CoolBasis
open Bwd
open BwdNotation

module CmpL =
struct
  type local =
    {state : St.t;
     veil : Veil.t;
     cof_env : CofEnv.env}
end

module EvL =
struct
  type local =
    {state : St.t;
     veil : Veil.t;
     cof_env : CofEnv.env;
     env : D.env}
end

module QuL =
struct
  type local =
    {state : St.t;
     cof_env : CofEnv.env;
     veil : Veil.t;
     size : int}
end


module CmpM =
struct
  module M = Monad.MonadReaderResult (CmpL)
  open Monad.Notation (M)

  let read_global =
    let+ {state} = M.read in
    state

  let lift_ev env m CmpL.{state; cof_env; veil} =
    m EvL.{state; cof_env; veil; env}

  let read_veil =
    let+ {veil} = M.read in
    veil

  let test_sequent cx phi =
    let+ {cof_env} = M.read in
    CofEnv.test_sequent cof_env cx phi

  let abort_if_inconsistent : 'a -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.consistency st.cof_env with
    | `Consistent -> m st
    | `Inconsistent -> M.ret abort st

  include M
  include CmpL
end

type 'a compute = 'a CmpM.m

module EvM =
struct

  module M = Monad.MonadReaderResult (EvL)
  open Monad.Notation (M)

  let read_global =
    let+ {state} = M.read in
    state

  let read_local =
    let+ {env} = M.read in
    env

  let read_veil =
    let+ {veil} = M.read in
    veil

  let append cells =
    M.scope @@ fun local ->
    {local with env = {local.env with conenv = local.env.conenv <>< cells}}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun {state; cof_env; veil} ->
    m {state; cof_env; veil}

  let abort_if_inconsistent : 'a -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.consistency st.cof_env with
    | `Consistent -> m st
    | `Inconsistent -> M.ret abort st


  include EvL
  include M
end

type 'a evaluate = 'a EvM.m

module QuM =
struct

  module M = Monad.MonadReaderResult (QuL)
  module MU = Monad.Util (M)
  module CM = CofEnv.M (M)
  open Monad.Notation (M)

  let read_global =
    let+ {state} = M.read in
    state

  let read_local =
    let+ {size} = M.read in
    size

  let read_veil =
    let+ {veil} = M.read in
    veil

  let binder i =
    M.scope @@ fun local ->
    {local with size = i + local.size}

  let abort_if_inconsistent : 'a -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.consistency st.cof_env with
    | `Consistent -> m st
    | `Inconsistent -> M.ret abort st

  let lift_cmp (m : 'a compute) : 'a m =
    fun {state; veil; cof_env} ->
    m {state; veil; cof_env}

  let replace_env cof_env m =
    M.scope (fun local -> {local with cof_env}) @@
    abort_if_inconsistent `Abort @@
    let+ x = m in
    `Ret x

  let restrict phi m =
    let* {cof_env} = M.read in
    replace_env (CofEnv.assume cof_env phi) m

  let left_invert_under_cofs phis m =
    let* {cof_env} = M.read in
    CM.left_invert_under_cofs cof_env phis @@
    fun cof_env ->
    let+ _ = replace_env cof_env m in ()

  let left_invert_under_current_cof m = left_invert_under_cofs [] m

  let bind_cof_proof phi m =
    restrict phi @@ binder 1 m

  let top_var tp =
    let+ n = read_local in
    D.mk_var tp @@ n - 1

  let bind_var ~abort tp m =
    match tp with
    | D.TpPrf phi ->
      begin
        begin
          bind_cof_proof phi @@
          let* var = top_var tp in
          m var
        end |>> function
        | `Ret tm -> M.ret tm
        | `Abort -> M.ret abort
      end
    | _ ->
      binder 1 @@
      let* var = top_var tp in
      m var

  let bind_var_ = bind_var ~abort:()

  include QuL
  include M
end

type 'a quote = 'a QuM.m


module ElabM =
struct
  module Env = ElabEnv
  module M = Monad.MonadReaderStateResult (struct type global = St.t type local = Env.t end)
  include M

  let globally m =
    m |> scope @@ fun env ->
    Env.set_veil (Env.get_veil env) Env.init

  let emit ?(lvl = `Info) loc pp a : unit m =
    fun (st, _env) ->
    Log.pp_message ~loc ~lvl pp a;
    Ok (), st

  let veil v =
    M.scope @@ fun env ->
    Env.set_veil v env

  let lift_qu (m : 'a quote) : 'a m =
    fun (state, env) ->
    match QuM.run {state; cof_env = Env.cof_env env; veil = Env.get_veil env; size = Env.size env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_ev (m : 'a evaluate) : 'a m =
    fun (state, env) ->
    match EvM.run {state; veil = Env.get_veil env; cof_env = Env.cof_env env; env = Env.sem_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m =
    fun (state, env) ->
    match CmpM.run {state; veil = Env.get_veil env; cof_env = Env.cof_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let abort_if_inconsistent : 'a -> 'a m -> 'a m =
    fun abort m ->
    fun (state, env) ->
    match CofEnv.consistency (Env.cof_env env) with
    | `Consistent -> m (state, env)
    | `Inconsistent -> M.ret abort (state, env)
end
