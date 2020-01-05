module D = Domain
module S = Syntax
module St = ElabState

type 'a compute = St.t -> 'a
type 'a evaluate = St.t * D.env -> 'a
type 'a quote = St.t * int -> 'a

module CmpM =
struct
  type 'a m = 'a compute 
  let ret a _ = a
  let bind m k st = k (m st) st
  let run m st = m st
  let read st = st
  let throw exn _ = raise exn
end

module EvM =
struct
  type 'a m = 'a evaluate 
  let ret a _ = a
  let bind m k p = k (m p) p
  let run m st env = m (st, env)
  let read_global (st, _) = st
  let read_local (_, env) = env
  let throw exn _ = raise exn

  let push cells m (st, (env : D.env)) = 
    m (st, D.{locals = cells @ env.locals})

  let close_tp tp : _ m =
    fun (_, env) ->
    D.Clo {term = tp; env}

  let close_tm t : _ m = 
    fun (_, env) ->
    D.Clo {term = t; env}

  let close2_tm t : _ m = 
    fun (_, env) ->
    D.Clo2 {term = t; env}

  let close2_tp tp : _ m =
    fun (_, env) ->
    D.Clo2 {term = tp; env}

  let close3_tp tp : _ m = 
    fun (_, env) ->
    D.Clo3 {term = tp; env}

  let compute m (st, _) = m st
end

module QuM =
struct
  type 'a m = 'a quote
  let ret a _ = a
  let bind m k p = k (m p) p
  let run m st i = m (st, i)
  let read_global (st, _) = st
  let read_local (_, i) = i
  let throw exn _ = raise exn

  let push i m (st, n) = 
    m (st, i + n) 

  let compute m (st, _) = m st
end