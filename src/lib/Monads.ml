module D = Domain
module S = Syntax
module St = ElabState
open CoolBasis
open Bwd 
open BwdNotation

module CmpM =
struct
  module M = Monad.MonadReaderResult (struct type local = St.t * Restriction.t end)
  open Monad.Notation (M)
  include M

  let lift_ev env m (st, rst) = m (st, rst, env)

  let compare_dim r s = 
    let+ (_, rst) = read in 
    Restriction.compare rst r s

  let equal_dim r s = 
    let+ (_, rst) = read in 
    Restriction.equal rst r s

  let test_sequent cx phi =
    let+ (_, rst) = read in 
    Restriction.test_sequent rst cx phi 
end

type 'a compute = 'a CmpM.m

module EvM =
struct
  module E =
  struct
    type local = St.t * Restriction.t * D.env
  end

  module M = Monad.MonadReaderResult (E)
  open Monad.Notation (M)

  let read_global =
    let+ (st,_, _) = M.read in 
    st

  let read_local =
    let+ (_, _, env) = M.read in 
    env

  let append cells = 
    M.scope @@ fun (st, rst, env) ->
    st, rst, env <>< cells

  let close_tp tp : _ m =
    let+ env = read_local in 
    D.Clo {bdy = tp; env}

  let close_tm t : _ m = 
    let+ env = read_local in 
    D.Clo {bdy = t; env}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun (st, rst, _) ->
    m (st, rst)

  include E
  include M
end

type 'a evaluate = 'a EvM.m

module QuM =
struct
  module E = 
  struct
    type local = St.t * Restriction.t * Veil.t * int
  end

  module M = Monad.MonadReaderResult (E)
  open Monad.Notation (M)

  let read_global =
    let+ (st, _, _, _) = M.read in 
    st

  let read_local =
    let+ (_, _, _, size) = M.read in 
    size

  let read_veil = 
    let+ (_, _, veil, _) = M.read in
    veil

  let binder i =
    M.scope @@ fun (st, rst, veil, size) ->
    st, rst, veil, i + size

  let lift_cmp (m : 'a compute) : 'a m = 
    fun (st, rst, _, _) ->
    m (st, rst)

  let under_dim_eq_ r s m =
    fun (st, rst, veil, size) ->
    match Restriction.equate rst r s with
    | exception Restriction.Inconsistent -> 
      Result.Ok ()
    | rst' ->
      m (st, rst', veil, size)


  let rec under_cofs_ cx m = 
    match cx with 
    | [] -> m

    | Cof.Eq (r, s) :: cx -> 
      under_dim_eq_ r s @@ 
      under_cofs_ cx m

    | Cof.Join (phi, psi) :: cx -> 
      let+ () = under_cofs_ (phi :: cx) m 
      and+ () = under_cofs_ (psi :: cx) m in 
      ()

    | Cof.Meet (phi, psi) :: cx ->
      under_cofs_ (phi :: psi :: cx) m


  include E
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
    fun (st, env) ->
    match QuM.run (st, Env.restriction env, Env.get_veil env, Env.size env) m with 
    | Ok v -> Ok v, st
    | Error exn -> Error exn, st

  let lift_ev (m : 'a evaluate) : 'a m = 
    fun (st, env) ->
    match EvM.run (st, Env.restriction env, Env.sem_env env) m with 
    | Ok v -> Ok v, st 
    | Error exn -> Error exn, st

  let lift_cmp (m : 'a compute) : 'a m = 
    fun (st, env) ->
    match CmpM.run (st, Env.restriction env) m with
    | Ok v -> Ok v, st 
    | Error exn -> Error exn, st
end