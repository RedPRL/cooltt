module D = Domain
module S = Syntax
module St = ElabState
open CoolBasis
open Bwd 
open BwdNotation

module CmpM =
struct
  include Monad.MonadReaderResult (struct type local = St.t end)
  let lift_ev env m st = m (st, env)
end

type 'a compute = 'a CmpM.m

module EvM =
struct
  module M = Monad.MonadReaderResult (struct type local = St.t * D.env end)
  open Monad.Notation (M)

  let read_global =
    let+ (st, _) = M.read in 
    st

  let read_local =
    let+ (_, env) = M.read in 
    env

  let append cells = 
    M.scope @@ fun (st, env) ->
    st, D.{locals = env.locals <>< cells}

  let close_tp tp : _ m =
    let+ env = read_local in 
    D.Clo {bdy = tp; env}

  let close_tm t : _ m = 
    let+ env = read_local in 
    D.Clo {bdy = t; env}

  let lift_cmp (m : 'a compute) : 'a M.m =
    fun (st, _) ->
    m st

  include M
end

type 'a evaluate = 'a EvM.m

module QuM =
struct
  module M = Monad.MonadReaderResult (struct type local = St.t * int end)
  open Monad.Notation (M)

  let read_global =
    let+ (st, _) = M.read in 
    st

  let read_local =
    let+ (_, size) = M.read in 
    size

  let append i =
    M.scope @@ fun (st, size) ->
    st, i + size

  let lift_cmp m (st, _) = m st

  include M
end

type 'a quote = 'a QuM.m


module ElabM = 
struct
  module Env = ElabEnv
  module M = Monad.MonadReaderStateResult (struct type global = St.t type local = Env.t end)
  include M

  let globally m =
    m |> scope @@ fun _ -> Env.init

  let emit pp a : unit m = 
    fun (st, _env) -> 
    let () = Format.fprintf Format.std_formatter "%a@." pp a in 
    Ok (), st


  let lift_qu (m : 'a quote) : 'a m = 
    fun (st, env) ->
    match QuM.run (st, Env.size env) m with 
    | Ok v -> Ok v, st
    | Error exn -> Error exn, st

  let lift_ev (m : 'a evaluate) : 'a m = 
    fun (st, env) ->
    match EvM.run (st, Env.sem_env env) m with 
    | Ok v -> Ok v, st 
    | Error exn -> Error exn, st

  let lift_cmp (m : 'a compute) : 'a m = 
    fun (st, _env) ->
    match CmpM.run st m with
    | Ok v -> Ok v, st 
    | Error exn -> Error exn, st
end