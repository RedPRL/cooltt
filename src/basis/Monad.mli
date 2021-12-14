open Bwd

module type S = sig
  type 'a m

  val ret : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module type Notation = sig
  type 'a m

  val (let*) : 'a m -> ('a -> 'b m) -> 'b m
  val (and*) : 'a m -> 'b m -> ('a * 'b) m
  val (let+) : 'a m -> ('a -> 'b) -> 'b m
  val (and+) : 'a m -> 'b m -> ('a * 'b) m

  val (<@>) : ('a -> 'b) -> 'a m -> 'b m
  val (|>>) : 'a m -> ('a -> 'b m) -> 'b m
  val (@<<) : ('a -> 'b m) -> 'a m -> 'b m
  val (<&>) : 'a m -> 'b m -> ('a * 'b) m
end

module Notation (M : S) : Notation with type 'a m = 'a M.m

module Util (M : S) : sig
  val commute_list : 'a M.m list -> 'a list M.m
  val map : ('a -> 'b M.m) -> 'a list -> 'b list M.m
  val filter_map : ('a -> 'b option M.m) -> 'a list -> 'b list M.m
  val map_bwd : ('a -> 'b M.m) -> 'a bwd -> 'b bwd M.m
  val iter : ('a -> unit M.m) -> 'a list -> unit M.m
  val ignore : 'a M.m -> unit M.m
  val fold_left_m : ('a -> 'b ->'b M.m) -> 'b -> 'a list -> 'b M.m
  val guard : bool -> (unit -> unit M.m) -> unit M.m
  val assoc_map : ('b -> 'c M.m) -> ('a * 'b) list -> ('a * 'c) list M.m
  val commute_assoc : ('a * 'b M.m) list -> ('a * 'b) list M.m
  val map_accum_left_m : ('a list -> 'a -> 'b M.m) -> 'a list -> ('b list) M.m
end

module type MonadReaderResult = sig
  include S
  type local
  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val run : local -> 'a m -> ('a, exn) result
  val run_exn : local -> 'a m -> 'a
  val throw : exn -> 'a m

  val trap : 'a m -> ('a, exn) result m
end

module type MonadReaderStateResult = sig
  include S
  type global
  type local

  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val get : global m
  val set : global -> unit m
  val modify : (global -> global) -> unit m

  val run : global -> local -> 'a m -> ('a, exn) result
  val run_exn : global -> local -> 'a m -> 'a
  val run_globals_exn : global -> local -> 'a m -> ('a * global)
  val throw : exn -> 'a m
  val trap : 'a m -> ('a, exn) result m
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
