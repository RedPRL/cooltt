module D = Domain
module S = Syntax
module St = ElabState
open CoolBasis
open Bwd
open BwdNotation

exception CCHM
exception CJHM
exception CFHM

module CmpL =
struct
  type local =
    {state : St.t;
     cof_env : CofEnv.env}
end

module EvL =
struct
  type local =
    {state : St.t;
     cof_env : CofEnv.env;
     env : D.env}
end

module QuL =
struct
  type local =
    {state : St.t;
     veil : Veil.t;
     cof_reduced_env : CofEnv.reduced_env;
     size : int}
end


module CmpM =
struct
  module M = Monad.MonadReaderResult (CmpL)
  open Monad.Notation (M)

  let read_global =
    let+ {state} = M.read in
    state

  let lift_ev env m CmpL.{state; cof_env} =
    m EvL.{state; cof_env; env}

  let read_cof_env =
    let+ {cof_env} = M.read in
    cof_env

  let test_sequent cx phi =
    let+ {cof_env} = M.read in
    CofEnv.test_sequent cof_env cx phi

  let restore_cof_env cof_env =
    M.scope @@ fun local ->
    {local with cof_env}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.consistency st.cof_env with
    | `Consistent -> m st
    | `Inconsistent -> abort st

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

  let append cells =
    M.scope @@ fun local ->
    {local with env = {local.env with conenv = local.env.conenv <>< cells}}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun {state; cof_env} ->
    m {state; cof_env}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.consistency st.cof_env with
    | `Consistent -> m st
    | `Inconsistent -> abort st


  include EvL
  include M
end

type 'a evaluate = 'a EvM.m

module QuM =
struct

  module M = Monad.MonadReaderResult (QuL)
  module MU = Monad.Util (M)
  open Monad.Notation (M)
  type 'a m' = CofEnv.cof list -> 'a m

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

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofEnv.Reduced.consistency st.cof_reduced_env with
    | `Consistent -> m st
    | `Inconsistent -> abort st

  let lift_cmp (m : 'a compute) : 'a m =
    fun {state; cof_reduced_env} ->
    m {state; cof_env = CofEnv.Reduced.to_env cof_reduced_env}

  let lift_cmp_under_cofs phis (m : 'a compute) : 'a m =
    fun {state; cof_reduced_env} ->
    m {state; cof_env = CofEnv.Reduced.assemble_env cof_reduced_env phis}

  let replace_env ~(abort : 'a m) (cof_reduced_env : CofEnv.reduced_env) (m : 'a m) : 'a m =
    M.scope (fun local -> {local with cof_reduced_env}) @@
    abort_if_inconsistent abort m

  let restrict ~(splitter:(D.cof * 'a m) list -> 'a m) phis (m : 'a m) : 'a m =
    let seq f cofs =
      splitter @@ List.map (fun cof -> cof , f cof) cofs
    in
    let* {cof_reduced_env} = M.read in
    CofEnv.Reduced.left_invert_under_cofs
      ~zero:(splitter []) ~seq
      cof_reduced_env phis @@ fun reduced_env ->
    replace_env ~abort:(splitter []) reduced_env m

  let restrict_ phis m =
    let* {cof_reduced_env} = M.read in
    CofEnv.Reduced.left_invert_under_cofs
      ~zero:(M.ret ()) ~seq:MU.iter
      cof_reduced_env phis @@ fun reduced_env ->
    replace_env ~abort:(M.ret ()) reduced_env m

  let top_var tp =
    let+ n = read_local in
    D.mk_var tp @@ n - 1

  let bind'_var tp m =
    binder 1 @@
    let* var = top_var tp in
    m var @@
    match tp with
    | D.TpPrf phi -> [phi]
    | _ -> []

  let bind_var ~splitter tp m =
    bind'_var tp @@ fun var phis ->
    restrict ~splitter phis @@ m var

  let bind_var_ tp m =
    bind'_var tp @@
    fun var phis -> restrict_ phis @@ m var

  include QuL
  include M
end

type 'a quote = 'a QuM.m
type 'a quote' = CofEnv.cof list -> 'a quote


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

  let lift_qu (m : 'a quote') : 'a m =
    fun (state, env) ->
    let cof_reduced_env, unreduced_phis =
      CofEnv.Reduced.partition_env @@ Env.cof_env env
    in
    match
      QuM.run {state; cof_reduced_env; veil = Env.get_veil env; size = Env.size env} @@
      m unreduced_phis
    with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_qu_ (m : unit quote) : unit m =
    lift_qu @@ fun phis -> QuM.restrict_ phis m

  let lift_ev (m : 'a evaluate) : 'a m =
    fun (state, env) ->
    match EvM.run {state; cof_env = Env.cof_env env; env = Env.sem_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m =
    fun (state, env) ->
    match CmpM.run {state; cof_env = Env.cof_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun (state, env) ->
    match CofEnv.consistency (Env.cof_env env) with
    | `Consistent -> m (state, env)
    | `Inconsistent -> abort (state, env)
end
