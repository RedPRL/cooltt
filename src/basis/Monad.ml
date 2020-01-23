module type S = sig
  type 'a m

  val ret : 'a -> 'a m

  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module type Notation = sig
  type 'a m

  val ( let* ) : 'a m -> ('a -> 'b m) -> 'b m

  val ( let+ ) : 'a m -> ('a -> 'b) -> 'b m

  val ( and+ ) : 'a m -> 'b m -> ('a * 'b) m
end

module Notation (M : S) : Notation with type 'a m = 'a M.m = struct
  type 'a m = 'a M.m

  let ( let* ) = M.bind

  let ( let+ ) m f = M.bind m (fun x -> M.ret (f x))

  let ( and+ ) m n =
    let* x = m in
    let* y = n in
    M.ret (x, y)
end

module type MonadReaderResult = sig 
  include S
  type local
  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val run : local -> 'a m -> ('a, exn) result
  val run_exn : local -> 'a m -> 'a
  val throw : exn -> 'a m
  val successful : unit m -> bool m
end

module type MonadReaderStateResult = sig 
  include S
  type global
  type local

  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val get : global m
  val set : global -> unit m

  val run : global -> local -> 'a m -> ('a, exn) result
  val run_exn : global -> local -> 'a m -> 'a
  val throw : exn -> 'a m
  val successful : unit m -> bool m
end



module MonadReaderResult (X : sig type local end) =
struct
  type 'a m = X.local -> ('a, exn) result

  let ret a _ = Ok a

  let bind m k env =
    match m env with 
    | Ok a -> k a env
    | Error exn -> Error exn

  let throw exn _ = Error exn

  let successful (m : unit m) : bool m =
    fun env ->
    match m env with
    | Ok _ -> Ok true
    | Error _ -> Ok false

  let read env = Ok env
  let scope f m env = m @@ f env

  let run env m = m env

  let run_exn env m =
    match run env m with 
    | Ok a -> a 
    | Error exn -> raise exn

end

module MonadReaderStateResult (X : sig type global type local end) = 
struct
  type 'a m = X.global * X.local -> ('a, exn) result * X.global

  let ret a (st, _) = Ok a, st

  let bind m k (st, env) = 
    match m (st, env) with 
    | Ok a, st' -> k a (st', env)
    | Error exn, st' -> Error exn, st'

  let throw exn (st, _) = Error exn, st


  let successful (m : unit m) : bool m =
    fun env ->
    match m env with
    | Ok _, st -> Ok true, st
    | Error _, st -> Ok false, st

  let read (st, env) = Ok env, st 

  let scope f m (st, env) = m (st, f env)
  let get (st, _) = Ok st, st
  let set st (_, _) = Ok (), st

  let run st env m = 
    let a, _ = m (st, env) in
    a

  let run_exn st env m =
    match run st env m with 
    | Ok a -> a 
    | Error exn -> raise exn 
end