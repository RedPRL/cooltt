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
     restriction : Restriction.t}
end

module EvL =
struct
  type local = 
    {state : St.t;
     restriction : Restriction.t; 
     env : D.env}
end

module QuL = 
struct
  type local = 
    {state : St.t;
     restriction : Restriction.t;
     veil : Veil.t;
     size : int}
end


module CmpM =
struct
  module M = Monad.MonadReaderResult (CmpL)
  open Monad.Notation (M)

  let lift_ev env m CmpL.{state; restriction} = 
    m EvL.{state; restriction; env}

  let compare_dim r s = 
    let+ {restriction} = M.read in 
    Restriction.compare restriction r s

  let equal_dim r s = 
    let+ {restriction} = M.read in 
    Restriction.equal restriction r s

  let test_sequent cx phi =
    let+ {restriction} = M.read in 
    Restriction.test_sequent restriction cx phi 

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
    fun {state; restriction} ->
    m {state; restriction}

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
    fun {state; restriction} ->
    m {state; restriction} 

  let restrict r s m =
    let* {restriction} = M.read in
    match Restriction.equate restriction r s with
    | exception Restriction.Inconsistent ->
      M.ret `Abort
    | restriction ->
      M.scope (fun local -> {local with restriction}) @@
      let+ x = m () in
      `Continue x

  let rec left_focus acc lfoc m = 
    match lfoc with 
    | [] -> 
      let+ x = m in 
      Cof.const acc x
    | `Eq (r, s) :: lfoc ->
      let+ result = 
        restrict r s @@ fun () ->
        left_focus (Cof.meet (Cof.eq r s) acc) lfoc m
      in 
      match result with 
      | `Abort -> Cof.abort 
      | `Continue x -> x

  let rec left_inversion (lfoc : [`Eq of D.dim * D.dim] list) (linv : D.dim Cof.cof list) (m : 'a m) : (D.dim, 'a) Cof.tree m =
    match linv with 
    | [] -> 
      left_focus Cof.top lfoc m
    | Cof.Eq (r, s) :: cx ->
      left_inversion (`Eq (r, s) :: lfoc) cx m
    | Cof.Join (phi, psi) :: cx ->
      let+ tree0 = left_inversion lfoc (phi :: cx) m 
      and+ tree1 = left_inversion lfoc (psi :: cx) m in
      Cof.split tree0 tree1
    | Cof.Bot :: _ ->
      M.ret @@ Cof.abort
    | Cof.Top :: linv ->
      left_inversion lfoc linv m
    | Cof.Meet (phi, psi) :: cx ->
      left_inversion lfoc (phi :: psi :: linv) m


  let under_cofs : D.dim Cof.cof list -> 'a m -> (D.dim, 'a) Cof.tree m =
    fun linv ->
    left_inversion [] linv

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
    match QuM.run {state; restriction = Env.restriction env; veil = Env.get_veil env; size = Env.size env} m with 
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_ev (m : 'a evaluate) : 'a m = 
    fun (state, env) ->
    match EvM.run {state; restriction = Env.restriction env; env = Env.sem_env env} m with 
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state

  let lift_cmp (m : 'a compute) : 'a m = 
    fun (state, env) ->
    match CmpM.run {state; restriction = Env.restriction env} m with
    | Ok v -> Ok v, state
    | Error exn -> Error exn, state
end