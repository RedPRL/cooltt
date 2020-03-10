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
     cof_env : CofEnv.env;
     veil : Veil.t;
     size : int}
end


module CmpM =
struct
  module M = Monad.MonadReaderResult (CmpL)
  open Monad.Notation (M)

  let lift_ev env m CmpL.{state; cof_env} = 
    m EvL.{state; cof_env; env}

  let test_sequent cx phi =
    let+ {cof_env} = M.read in 
    CofEnv.test_sequent cof_env cx phi 

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
    {local with env = local.env <>< cells}

  let close_tp tp : _ m =
    let+ env = read_local in 
    D.Clo {bdy = tp; env}

  let close_tm t : _ m = 
    let+ env = read_local in 
    D.Clo {bdy = t; env}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun {state; cof_env} ->
    m {state; cof_env}

  include EvL
  include M
end

type 'a evaluate = 'a EvM.m

module QuM =
struct

  module M = Monad.MonadReaderResult (QuL)
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

  let lift_cmp (m : 'a compute) : 'a m =   
    fun {state; cof_env} ->
    m {state; cof_env} 

  let restrict phi m =
    let* {cof_env} = M.read in
    let cof_env = CofEnv.assume cof_env phi in 
    match CofEnv.status cof_env with 
    | `Consistent -> 
      M.scope (fun local -> {local with cof_env}) @@
      let+ x = m () in
      `Continue x
    | `Inconsistent -> 
      M.ret `Abort


  module Search =
  struct
    type atomic = [`Eq of D.dim * D.dim | `Var of int]

    let as_cof =
      function
      | `Eq (r, s) -> Cof.eq r s
      | `Var lvl -> Cof.var lvl

    let rec atomics acc (xi : atomic list) m = 
      match xi with 
      | [] -> 
        let+ x = m in 
        Cof.const (acc, x)
      | phi :: xi ->
        let phi = as_cof phi in
        let+ result = 
          restrict phi @@ fun () ->
          atomics (Cof.meet phi acc) xi m
        in 
        begin
          match result with 
          | `Abort -> Cof.abort 
          | `Continue x -> x
        end

    let rec left_inversion (xi : atomic list) (linv : D.cof list) (m : 'a m) : (D.cof * 'a) Cof.tree m =
      match linv with 
      | [] -> 
        atomics Cof.top xi m
      | Cof.Cof (Cof.Eq (r, s)) :: cx ->
        left_inversion (`Eq (r, s) :: xi) cx m
      | Cof.Var v :: cx ->
        left_inversion (`Var v :: xi) cx m
      | Cof.Cof (Cof.Join (phi, psi)) :: cx ->
        let+ tree0 = binder 1 @@ left_inversion xi (phi :: cx) m 
        and+ tree1 = binder 1 @@ left_inversion xi (psi :: cx) m in
        Cof.split tree0 tree1
      | Cof.Cof Cof.Bot :: _ ->
        M.ret @@ Cof.abort
      | Cof.Cof Cof.Top :: linv ->
        left_inversion xi linv m
      | Cof.Cof (Cof.Meet (phi, psi)) :: cx ->
        left_inversion xi (phi :: psi :: linv) m
  end


  let under_cofs : D.cof list -> 'a m -> (D.cof * 'a) Cof.tree m =
    fun linv ->
    Search.left_inversion [] linv

  let under_cofs_ cx m = 
    let+ _ = under_cofs cx m in
    ()

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

  let emit pp a : unit m = 
    fun (st, _env) -> 
    let () = Format.fprintf Format.std_formatter "%a@." pp a in 
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
    match EvM.run {state; cof_env = Env.cof_env env; env = Env.sem_env env} m with 
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m = 
    fun (state, env) ->
    match CmpM.run {state; cof_env = Env.cof_env env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state
end