module D = Domain
module S = Syntax
module St = ElabState

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

  let push cells = 
    M.scope @@ fun (st, env) ->
    st, D.{locals = cells @ env.locals}

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

  let push i =
    M.scope @@ fun (st, size) ->
    st, i + size

  let lift_cmp m (st, _) = m st

  include M
end

type 'a quote = 'a QuM.m