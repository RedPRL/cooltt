open Basis
open Bwd

open CodeUnit

module D = Domain
module S = Syntax
module St = RefineState

exception CCHM
exception CJHM
exception CFHM

module CmpL =
struct
  type local =
    {state : St.t;
     cof_thy : CofThy.Disj.t}
end

module EvL =
struct
  type local =
    {state : St.t;
     cof_thy : CofThy.Disj.t;
     env : D.env}
end

module ConvL =
struct
  type local =
    {state : St.t;
     cof_thy : CofThy.Alg.t;
     size : int}
end

module QuL =
struct
  type local =
    {state : St.t;
     norm : bool;
     cof_thy : CofThy.Disj.t;
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
    CofThy.Disj.test_sequent cof_thy cx phi

  let simplify_cof phi =
    let+ {cof_thy; _} = M.read in
    CofThy.Disj.simplify_cof cof_thy phi

  let forall_cof (sym, phi) =
    let+ {cof_thy; _} = M.read in
    CofThy.Disj.forall_cof cof_thy (sym, phi)

  let restore_cof_thy cof_thy =
    M.scope @@ fun local ->
    {local with cof_thy}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.Disj.consistency st.cof_thy with
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
    let open Bwd.Infix in
    {local with env = {local.env with conenv = local.env.conenv <@ cells}}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun {state; cof_thy; _} ->
    m {state; cof_thy}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.Disj.consistency st.cof_thy with
    | `Consistent -> m st
    | `Inconsistent -> abort st


  include EvL
  include M
end

type 'a evaluate = 'a EvM.m

module ConvM =
struct

  module M = Monad.MonadReaderResult (ConvL)
  module MU = Monad.Util (M)
  open Monad.Notation (M)

  let read_local =
    let+ {size; _} = M.read in
    size

  let binder i =
    M.scope @@ fun local ->
    {local with size = i + local.size}

  let globally m =
    m |> M.scope @@ fun local ->
    {local with size = 0}

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.Alg.consistency st.cof_thy with
    | `Consistent -> m st
    | `Inconsistent -> abort st

  let lift_cmp (m : 'a compute) : 'a m =
    fun {state; cof_thy; _} ->
    m {state; cof_thy = CofThy.Disj.envelope_alg cof_thy}

  let replace_env cof_thy m =
    M.scope (fun local -> {local with cof_thy}) m

  let restrict_ phis m =
    let* {cof_thy; _} = M.read in
    MU.iter
      (fun thy -> replace_env thy m)
      (CofThy.Alg.split cof_thy phis)

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

  let bind_var_ tp m =
    bind'_var tp @@ fun var phis ->
    restrict_ phis @@ m var

  include ConvL
  include M
end

type 'a conversion = 'a ConvM.m

module QuM =
struct

  module M = Monad.MonadReaderResult (QuL)
  module MU = Monad.Util (M)
  open Monad.Notation (M)

  let read_global =
    let+ {state; _} = M.read in
    state

  let read_local =
    let+ {size; _} = M.read in
    size

  let lift_cmp (m : 'a compute) : 'a m =
    fun {state; cof_thy; _} ->
    m {state; cof_thy}

  let globally m =
    m |> M.scope @@ fun local ->
    {local with size = 0}

  let replace_env cof_thy =
    M.scope @@ fun local -> {local with cof_thy}

  let restrict phis m =
    let* {cof_thy; _} = M.read in
    replace_env (CofThy.Disj.assume cof_thy phis) m

  let binder i =
    M.scope @@ fun local ->
    {local with size = i + local.size}

  let should_normalize =
    let+ {norm; _} = M.read in
    norm

  let with_normalization norm =
    M.scope @@ fun local -> {local with norm}

  let top_var tp =
    let+ n = read_local in
    D.mk_var tp @@ n - 1

  let bind_var tp m =
    binder 1 @@
    let* var = top_var tp in
    match tp with
    | D.TpPrf phi -> restrict [phi] @@ m var
    | _ -> m var

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun st ->
    match CofThy.Disj.consistency st.cof_thy with
    | `Consistent -> m st
    | `Inconsistent -> abort st

  include QuL
  include M
end

type 'a quote = 'a QuM.m

module RefineM =
struct
  module Env = RefineEnv
  module M = Monad.MonadReaderStateResult (struct type global = St.t type local = Env.t end)
  include M

  let globally m (st, env) =
    scope Env.globally m (st, env)

  let emit ?(lvl = `Info) loc pp a : unit m =
    fun (st, _env) -> match lvl with
      | `Error ->
        Log.pp_error_message ~loc ~lvl pp a;
        Ok (), st
      | _ ->
        Log.pp_runtime_message ~loc ~lvl pp a;
        Ok (), st

  let restrict phis =
    M.scope (Env.restrict phis)

  let cof_thy st env = CofThy.Disj.meet2 (St.get_global_cof_thy st) (Env.local_cof_thy env)

  let lift_conv_ (m : unit conversion) : unit m =
    let module MU = Monad.Util (struct
        type 'a m = ('a, exn) result let ret = Result.ok let bind = Result.bind
      end)
    in
    fun (state, env) ->
      match
        MU.iter
          (fun cof_thy -> ConvM.run {state; cof_thy; size = Env.size env} m)
          (CofThy.Disj.decompose @@ cof_thy state env)
      with
      | Ok () -> Ok (), state
      | Error exn -> Error exn, state

  let lift_qu (m : 'a quote) : 'a m =
    fun (state, env) ->
    match
      QuM.run {state; cof_thy = cof_thy state env; norm = false; size = Env.size env} m
    with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_ev (m : 'a evaluate) : 'a m =
    fun (state, env) ->
    match EvM.run {state; cof_thy = cof_thy state env; env = Env.sem_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m =
    fun (state, env) ->
    match CmpM.run {state; cof_thy = cof_thy state env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let abort_if_inconsistent : 'a m -> 'a m -> 'a m =
    fun abort m ->
    fun (state, env) ->
    match CofThy.Disj.consistency (cof_thy state env) with
    | `Consistent -> m (state, env)
    | `Inconsistent -> abort (state, env)
end
