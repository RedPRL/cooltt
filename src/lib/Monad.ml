module type S = 
sig
  type 'a m 
  val ret : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module type Notation =
sig
  type 'a m
  val (let*) : 'a m -> ('a -> 'b m) -> 'b m
end

module Notation (M : S) : Notation with type 'a m = 'a M.m =
struct
  type 'a m = 'a M.m
  let (let*) = M.bind
end

