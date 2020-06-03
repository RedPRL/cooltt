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
     cof_thy : CofThy.disj_thy}
end

module EvL =
struct
  type local =
    {state : St.t;
     cof_thy : CofThy.disj_thy;
     env : D.env}
end

module ConvL =
struct
  type local =
    {state : St.t;
     veil : Veil.t;
     cof_thy : CofThy.alg_thy;
     size : int}
end


module CmpM =
struct
  module M = Monad.MonadReaderResult (CmpL)
  open Monad.Notation (M)

  let read_global =
    let+ {state; _} = M.read in
    state

  let lift_ev env m CmpL.{state; cof_thy} =
    m EvL.{state; cof_thy; env}

  let read_cof_thy =
    let+ {cof_thy; _} = M.read in
    cof_thy

  let test_sequent cx phi =
    let+ {cof_thy; _} = M.read in
    CofThy.test_sequent cof_thy cx phi

  let restore_cof_thy cof_thy =
    M.scope @@ fun local ->
    {local with cof_thy}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.consistency st.cof_thy with
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
    let+ {state; _} = M.read in
    state

  let read_local =
    let+ {env; _} = M.read in
    env

  exception Drop

  let drop_con (k : 'a m) : 'a m =
    let* {env; _} = M.read in
    match env.conenv with
    | Snoc (conenv, _) ->
      M.scope (fun local -> {local with env = {local.env with conenv}}) k
    | Emp ->
      M.throw Drop

  let drop_all_cons (k : 'a m) : 'a m =
    M.scope (fun local -> {local with env = {local.env with conenv = Emp}}) k

  let append cells =
    M.scope @@ fun local ->
    {local with env = {local.env with conenv = local.env.conenv <>< cells}}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun {state; cof_thy; _} ->
    m {state; cof_thy}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.consistency st.cof_thy with
    | `Consistent -> m st
    | `Inconsistent -> abort st


  include EvL
  include M
end

type 'a evaluate = 'a EvM.m

module ConvM =
struct

  (* XXX In a separate PR, many things in this module should
   * be moved to [QuM]. *)

  module M = Monad.MonadReaderResult (ConvL)
  module MU = Monad.Util (M)
  open Monad.Notation (M)

  let read_global =
    let+ {state; _} = M.read in
    state

  let read_local =
    let+ {size; _} = M.read in
    size

  let read_veil =
    let+ {veil; _} = M.read in
    veil

  let binder i =
    M.scope @@ fun local ->
    {local with size = i + local.size}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.Algebraic.consistency st.cof_thy with
    | `Consistent -> m st
    | `Inconsistent -> abort st

  let lift_cmp (m : 'a compute) : 'a m =
    fun {state; cof_thy; _} ->
    m {state; cof_thy = CofThy.Algebraic.disj_envelope cof_thy}

  let replace_env ~(abort : 'a m) (cof_thy : CofThy.alg_thy) (m : 'a m) : 'a m =
    M.scope (fun local -> {local with cof_thy}) @@
    abort_if_inconsistent abort m

  let restrict ~(splitter:(D.cof * 'a m) list -> 'a m) phis (m : 'a m) : 'a m =
    let seq f cofs =
      splitter @@ List.map (fun cof -> cof , f cof) cofs
    in
    let* {cof_thy; _} = M.read in
    CofThy.Algebraic.left_invert_under_cofs
      ~zero:(splitter []) ~seq
      cof_thy phis @@ fun alg_thy ->
    replace_env ~abort:(splitter []) alg_thy m

  let restrict_ phis m =
    let* {cof_thy; _} = M.read in
    CofThy.Algebraic.left_invert_under_cofs
      ~zero:(M.ret ()) ~seq:MU.iter
      cof_thy phis @@ fun alg_thy ->
    replace_env ~abort:(M.ret ()) alg_thy m

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
    bind'_var tp @@ fun var phis ->
    restrict_ phis @@ m var

  include ConvL
  include M
end

type 'a conversion = 'a ConvM.m

module QuM =
struct

  (* XXX In a separate PR, this should be using [Cof.env]
   * instead of [Cof.alg_thy * D.cof list]. The code
   * is correct now but is extremely low-ch'i. *)

  module M = struct
    type 'a m = CofThy.cof list -> 'a ConvM.m
    let bind m1 m2 cofs = ConvM.bind (m1 cofs) @@ fun x -> m2 x cofs
    let ret x _cofs = ConvM.ret x
  end
  module MU = Monad.Util (M)
  open Monad.Notation (M)

  type local = ConvM.local

  let run local m =
    ConvM.run local @@ m []

  let run_exn local m =
    ConvM.run_exn local @@ m []

  let trap m cofs =
    ConvM.trap @@ m cofs

  let throw exn _ =
    ConvM.throw exn

  let scope f m cofs =
    ConvM.scope f @@ m cofs

  let lift_cmp (m : 'a compute) : 'a m =
    fun phis {state; cof_thy; _} ->
    m {state; cof_thy = CofThy.Algebraic.assemble_thy cof_thy phis}

  let read _ =
    ConvM.read

  let read_global _ =
    ConvM.read_global

  let read_local _ =
    ConvM.read_local

  let read_veil _ =
    ConvM.read_veil

  let binder i m cofs =
    ConvM.binder i @@ m cofs

  let split cofs m = m cofs

  let seq ~splitter m cofs =
    ConvM.restrict ~splitter cofs m

  let seq_ m : 'a m =
    fun cofs ->
    ConvM.restrict_ cofs m

  let bind_var tp m cofs =
    ConvM.bind'_var tp @@ fun var cofs' ->
    m var @@ cofs @ cofs'

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m cofs ->
    fun st ->
    match
      CofThy.consistency @@
      CofThy.Algebraic.assemble_thy st.cof_thy cofs
    with
    | `Consistent -> m cofs st
    | `Inconsistent -> abort cofs st

  include M
end

type 'a quote = CofThy.cof list -> 'a conversion


module ElabM =
struct
  module Env = ElabEnv
  module M = Monad.MonadReaderStateResult (struct type global = St.t type local = Env.t end)
  include M

  let globally m =
    m |> scope @@ fun env ->
    Env.set_location (Env.location env) @@
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
    let cof_thy, irreducible_phis =
      CofThy.Algebraic.partition_thy @@ Env.cof_thy env
    in
    match
      ConvM.run {state; cof_thy; veil = Env.get_veil env; size = Env.size env} @@
      m irreducible_phis
    with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_conv_ (m : unit conversion) : unit m =
    lift_qu @@ QuM.seq_ m

  let lift_ev (m : 'a evaluate) : 'a m =
    fun (state, env) ->
    match EvM.run {state; cof_thy = Env.cof_thy env; env = Env.sem_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m =
    fun (state, env) ->
    match CmpM.run {state; cof_thy = Env.cof_thy env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun (state, env) ->
    match CofThy.consistency (Env.cof_thy env) with
    | `Consistent -> m (state, env)
    | `Inconsistent -> abort (state, env)
end
