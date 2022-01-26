(** Constructing values in the semantic domain that go underneath binders is
    very difficult! In general you need to be able to form exactly the right
    closure for each binder, and it is usually not obvious how to do this,
    and it usually involves some awful De Bruijn arithmetic.

    An alternative is to create a term in an extended context, and then
    evaluate that in an environment that contains the values you want to
    "splice" into it; then, the resulting value will have the desired behavior.
    This module, which is called [Splice] for lack of a better name,
    achieves this in an automatic way, avoiding all De Bruijn arithmetic.  *)
open CodeUnit

module S := Syntax
module D := Domain
module TB := TermBuilder

type 'a t

val con : D.con -> (S.t TB.m -> 'a t) -> 'a t
val cons : D.con list -> (S.t TB.m list -> 'a t) -> 'a t
val dim : D.dim -> (S.t TB.m -> 'a t) -> 'a t
val cof : D.cof -> (S.t TB.m -> 'a t) -> 'a t
val clo : D.tm_clo -> (S.t TB.m -> 'a t) -> 'a t
val tp : D.tp -> (S.tp TB.m -> 'a t) -> 'a t
val compile : 'a t -> D.env * 'a
val term : 'a TB.m -> 'a t

module Macro :
sig
  val tp_pequiv_in_v : r:D.dim -> pcode:D.con -> code:D.con -> S.tp t
  val commute_split : D.con -> D.cof list -> (S.t TB.m -> S.t TB.m) -> S.t t
end

module Bdry :
sig
  type bdry := D.cof * S.t t
  val box : r:D.dim -> r':D.dim -> phi:D.cof -> sides:D.con -> cap:D.con -> bdry
  val cap : r:D.dim -> r':D.dim -> phi:D.cof -> code:D.con -> box:D.con -> bdry

  val vin : r:D.dim -> pivot:D.con -> base:D.con -> bdry
  val vproj : r:D.dim -> pcode:D.con -> code:D.con -> pequiv:D.con -> v:D.con -> bdry

  val hcom : r:D.dim -> r':D.dim -> phi:D.cof -> bdy:D.con -> bdry
  val com : r:D.dim -> r':D.dim -> phi:D.cof -> bdy:D.con -> bdry
  val coe : r:D.dim -> r':D.dim -> bdy:D.con -> bdry

  val unstable_code : D.con D.unstable_code -> bdry
  val unstable_frm : D.cut -> D.unstable_frm -> bdry
end

module Tele :
sig
  val unfold : D.con -> D.con -> S.t t
end
