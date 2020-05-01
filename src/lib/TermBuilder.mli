(** A language for building terms without doing De Bruijn arithmetic. This module contains constructors
 * not only for the primitives of cubical type theory, but also for the more complex derived forms --
 * for instance, the algorithm of coercion and composition in various type connectives. *)

open CoolBasis

include Monad.S

type t := Syntax.t
type tp := Syntax.tp

type 'a b = t m -> 'a m
val scope : 'a b -> 'a m
val run : tplen:int -> conlen:int -> 'a m -> 'a
val lvl : int -> t m
val tplvl : int -> tp m

val lam : t b -> t m
val ap : t m -> t m list -> t m
val coe : t m -> t m -> t m -> t m -> t m
val hcom : t m -> t m -> t m -> t m -> t m -> t m
val com : t m -> t m -> t m -> t m -> t m -> t m
val let_ : t m -> t b -> t m
val pair : t m -> t m -> t m
val fst : t m -> t m
val snd : t m -> t m

val cof_split : tp m -> t m -> t b -> t m -> t b -> t m
val cof_abort : t m
val sub_out : t m -> t m
val sub_in : t m -> t m

val univ : tp m

val pi : tp m -> tp b -> tp m
val sg : tp m -> tp b -> tp m
val sub : tp m -> t m -> t b -> tp m
val tp_prf : t m -> tp m
val tp_dim : tp m
val el : t m -> tp m

val dim0 : t m
val dim1 : t m
val eq : t m -> t m -> t m
val join : t m -> t m -> t m
val meet : t m -> t m -> t m
val boundary : t m -> t m

module Kan : sig
  type coe = r:t m -> s:t m -> bdy:t m -> t m
  type hcom = r:t m -> s:t m -> phi:t m -> bdy:t m -> t m

  val coe_pi : base_line:t m -> fam_line:t m -> coe
  val hcom_pi : base:t m -> fam:t m -> hcom

  val coe_sg : base_line:t m -> fam_line:t m -> coe
  val hcom_sg : base:t m -> fam:t m -> hcom

  val coe_path : fam_line:t m -> bdry_line:t m -> coe
  val hcom_path : fam:t m -> bdry:t m -> hcom
end
