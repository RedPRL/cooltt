module S := Syntax
module D := Domain
module TB := TermBuilder

type 'a builder
val foreign : D.con -> (S.t TB.m -> 'a builder) -> 'a builder
val compile : 'a builder -> D.env * 'a
val term : 'a TB.m -> 'a builder
