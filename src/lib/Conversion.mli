(** The purpose of this module is to check whether two {i well-typed} objects are equal or not. The semantics are that all definitions are unfolded, regardless of the "veil", since definitional equality is closed under unfolding of definitions. *)

module D := Domain
open Basis
open Monads

module Error :
sig
  type t
  val pp : t Pp.printer
end

exception ConversionError of Error.t

val equate_con : D.tp -> D.con -> D.con -> unit conversion
val equate_tp : D.tp -> D.tp -> unit conversion
