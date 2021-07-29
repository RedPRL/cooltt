open Basis

(** {1 Types} *)

module Make : functor (Symbol : Symbol.S) -> sig
  include module type of SyntaxData.Make(Symbol)

  (** {1 Convenience constructors} *)
  val tm_abort : t
  val tp_abort : tp

  (** {1 Pretty printers} *)

  (** {2 For display}
      These pretty printers are context sensitive, in order to recall user-specified names for binders. *)

  (** Print a core language term. *)
  val pp : Pp.env -> t Pp.printer

  (** Print a signature. *)
  val pp_sign : Pp.env -> sign Pp.printer

  (** Print a core language type. *)
  val pp_tp : Pp.env -> tp Pp.printer

  (** Vertically print an iterated dependent product type as if it were a sequent, for display of goals. *)
  val pp_sequent : lbl:string option -> (Ident.t * tp) list -> tp Pp.printer

  (** Vertically print an iterated dependent product type as if it were a sequent, for display of goals.
      This variant will also print out a partially constructed terms, as well as display if the boundary
      conditions are met. *)
  val pp_partial_sequent : bdry_sat:bool -> (Ident.t * tp) list -> (t * tp) Pp.printer

  (** {2 For debugging}
      When debugging, we are not likely to have enough context to use the nice pretty printers above; as a last resort, {!val:dump} and {!val:dump_tp} may be used. *)

  val dump : t Pp.printer
  val dump_sign : sign Pp.printer
  val dump_tp : tp Pp.printer
end
