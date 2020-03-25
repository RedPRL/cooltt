(** A language for building terms without doing De Bruijn arithmetic. This module contains constructors
 * not only for the primitives of cubical type theory, but also for the more complex derived forms --
 * for instance, the algorithm of coercion and composition in various type connectives. *)

open CoolBasis

include Monad.S

type t := Syntax.t

type 'a b = t m -> 'a m
val scope : 'a b -> 'a m
val run : len:int -> 'a m -> 'a
val lvl : int -> t m

val lam : t b -> t m
val coe : t m -> t m -> t m -> t m -> t m
val hcom : t m -> t m -> t m -> t m -> t m -> t m
val com : t m -> t m -> t m -> t m -> t m -> t m
val let_ : t m -> t b -> t m
val pair : t m -> t m -> t m
val fst : t m -> t m
val snd : t m -> t m


val coe_pi
  : base_line:t m
  -> fam_line:t m
  -> r:t m
  -> s:t m
  -> bdy:t m
  -> t m

val coe_sg
  : base_line:t m
  -> fam_line:t m
  -> r:t m
  -> s:t m
  -> bdy:t m
  -> t m

val hcom_pi
  : base:t m
  -> fam:t m
  -> r:t m
  -> s:t m
  -> phi:t m
  -> bdy:t m
  -> t m

val hcom_sg
  : base:t m
  -> fam:t m
  -> r:t m
  -> s:t m
  -> phi:t m
  -> bdy:t m
  -> t m

