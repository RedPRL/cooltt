(** {1 Types} *)

open Basis

module Make : functor (Symbol : Symbol.S) -> sig

  include module type of DomainData.Make(Symbol)

  (** {1 Convenience constructors} *)

  val dim_to_con : dim -> con
  val cof_to_con : cof -> con
  val mk_var : tp -> int -> con
  val push : frm -> cut -> cut

  val const_tm_clo : con -> tm_clo
  val const_tp_clo : tp -> tp_clo

  val un_lam : con -> tm_clo
  val compose : con -> con -> con
  val apply_to : con -> tm_clo

  val fst : con
  val snd : con
  val proj : Ident.t -> con
  val el_out : con

  val tm_abort : con
  val tp_abort : tp

  val sign_lbls : sign -> Ident.t list

  (** {1 Pretty-printers }

      These are only for debugging. *)

  val pp_dim : dim Pp.printer
  val pp_clo : tm_clo Pp.printer
  val pp_cof : cof Pp.printer
  val pp_tp : tp Pp.printer
  val pp_con : con Pp.printer
  val pp_cut : cut Pp.printer
  val pp_hd : hd Pp.printer
  val pp_frame : frm Pp.printer
  val pp_spine : frm list Pp.printer
  val pp_sign : sign Pp.printer
  val pp_env : env Pp.printer
end
