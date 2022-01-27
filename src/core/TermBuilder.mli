(** A language for building terms without doing De Bruijn arithmetic. This module contains constructors
 * not only for the primitives of cubical type theory, but also for the more complex derived forms --
 * for instance, the algorithm of coercion and composition in various type connectives. *)

open Basis
open CodeUnit

include Monad.S

module S := Syntax

type t := S.t
type tp := S.tp

type 'a b = t m -> 'a m
val scope : 'a b -> 'a m
val run : tplen:int -> conlen:int -> 'a m -> 'a
val lvl : int -> t m
val tplvl : int -> tp m

val lam : ?ident:Ident.t -> t b -> t m
val ap : t m -> t m list -> t m
val coe : t m -> t m -> t m -> t m -> t m
val hcom : t m -> t m -> t m -> t m -> t m -> t m
val com : t m -> t m -> t m -> t m -> t m -> t m
val let_ : ?ident:Ident.t -> t m -> t b -> t m
val pair : t m -> t m -> t m
val fst : t m -> t m
val snd : t m -> t m

val lams : Ident.t list -> (t m list -> t m) -> t m

val tele : tp m
val code_tele : t m
val nil : t m
val cons : Ident.user -> t m -> t m -> t m
val tele_elim : t m -> t m -> t m -> t m -> t m

val struct_ : (Ident.user * t m) list -> t m
val proj : t m -> Ident.user -> t m

val zero : t m
val suc : t m -> t m

val base : t m
val loop : t m -> t m

val prf : t m

val cap : t m -> t m -> t m -> t m -> t m -> t m
val box : t m -> t m -> t m -> t m -> t m -> t m

val cof_split : (t m * t m) list -> t m
val tp_cof_split : (t m * tp m) list -> tp m
val tm_abort : t m
val sub_out : t m -> t m
val sub_in : t m -> t m

val el_in : t m -> t m
val el_out : t m -> t m

val univ : tp m
val nat : tp m
val code_nat : t m
val nat_elim : t m -> t m -> t m -> t m -> t m

val circle : tp m
val code_circle : t m
val circle_elim : t m -> t m -> t m -> t m -> t m

val pi : ?ident:Ident.t -> tp m -> tp b -> tp m
val sg : ?ident:Ident.t -> tp m -> tp b -> tp m
val signature : t m -> tp m
val sub : tp m -> t m -> t b -> tp m
val tp_prf : t m -> tp m
val tp_dim : tp m
val tp_cof : tp m
val el : t m -> tp m

val pis: ?idents:Ident.t list -> t m list -> (t m list -> tp m) -> tp m

val tp_locked_prf : t m -> tp m
val locked_prf_in : t m -> t m
val locked_prf_unlock : tp m -> cof:t m -> prf:t m -> bdy:t m -> t m

val cube : int -> (t m list -> tp m) -> tp m

val code_univ : t m
val code_pi : t m -> t m -> t m
val code_sg : t m -> t m -> t m
val code_path : t m -> t m -> t m
val code_v : t m -> t m -> t m -> t m -> t m
val code_ext : int -> t m -> t m -> t m -> t m
val vproj : t m -> t m -> t m -> t m -> t m -> t m

val code_pis : t m list -> (t m list -> t m) -> t m

val dim0 : t m
val dim1 : t m
val eq : t m -> t m -> t m
val join : t m list -> t m
val meet : t m list -> t m
val top : t m
val bot : t m
val boundary : t m -> t m
val forall : t b -> t m


module Equiv : sig
  val code_is_contr : t m -> t m
  val code_fiber : t m -> t m -> t m -> t m -> t m
  val code_equiv : t m -> t m -> t m
  val equiv_fwd : t m -> t m
  val equiv_inv : t m -> t m -> t m
  val equiv_inv_path : t m -> t m -> t m -> t m
end


module Kan : sig
  type coe = r:t m -> r':t m -> bdy:t m -> t m
  type hcom = r:t m -> r':t m -> phi:t m -> bdy:t m -> t m

  val coe_pi : base_line:t m -> fam_line:t m -> coe
  val hcom_pi : fam:t m -> hcom

  val coe_sg : base_line:t m -> fam_line:t m -> coe
  val hcom_sg : base:t m -> fam:t m -> hcom

  val coe_sign : field_lines:(Ident.user * t m) list -> coe
  val hcom_sign : fields:(Ident.user * t m) list -> hcom

  val hcom_ext : n:int -> cof:t m -> fam:t m -> bdry:t m -> hcom
  val coe_ext : n:int -> cof:t m -> fam_line:t m -> bdry_line:t m -> coe

  module V : sig
    type vcode = {r : t m; pcode : t m; code : t m; pequiv : t m}
    val hcom_v : v:vcode -> r:t m -> r':t m -> phi:t m -> bdy:t m -> t m
    val coe_v : v:vcode -> r:t m -> r':t m -> bdy:t m -> t m
  end

  module FHCom : sig
    type fhcom_u = {r : t m; r' : t m; phi : t m; bdy : t m}
    val hcom_fhcom : fhcom:fhcom_u -> r:t m -> r':t m -> phi:t m -> bdy:t m -> t m
    val coe_fhcom : fhcom:fhcom_u -> r:t m -> r':t m -> bdy:t m -> t m
  end
end

module Test : sig
  val print_example : unit -> unit
end
