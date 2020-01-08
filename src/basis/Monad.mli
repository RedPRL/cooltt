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

module Notation (M : S) : Notation with type 'a m = 'a M.m

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
end

module MonadReaderResult (X : sig type local end) : sig 
  include MonadReaderResult
    with type 'a m = X.local -> ('a, exn) result
    with type local := X.local
end

module MonadReaderStateResult (X : sig type global type local end) : sig
  include MonadReaderStateResult 
    with type 'a m = X.global * X.local -> ('a, exn) result * X.global
    with type global := X.global
    with type local := X.local
end