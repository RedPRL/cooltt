open Basis

(** {1 Types} *)

module Make : functor (Symbol : Symbol.S) -> sig
  include module type of SyntaxData.Make(Symbol)

  (** {1 Convenience constructors} *)
  val tm_abort : t
  val tp_abort : tp

  val tele_lbls : tele -> Ident.t list
  val kan_tele_lbls : kan_tele -> Ident.t list

  (** Append two kan telescopes together.
      INVARIANT: The second telescope is well-scoped with regard to the first. *)
  val append_kan_tele : kan_tele -> kan_tele -> kan_tele

  (** {1 Pretty printers} *)

  (** {2 For display}
      These pretty printers are context sensitive, in order to recall user-specified names for binders. *)

  (** Print a core language term. *)
  val pp : Pp.env -> t Pp.printer

  (** Print a signature. *)
  val pp_tele : Pp.env -> tele Pp.printer

  (** Print a core language type. *)
  val pp_tp : Pp.env -> tp Pp.printer

  (** Vertically print an iterated dependent product type as if it were a sequent, for display of goals. *)
  val pp_sequent : lbl:string option -> (Ident.t * tp) list -> tp Pp.printer

  (** Vertically print an iterated dependent product type as if it were a sequent, for display of goals.
      This variant will also print out a partially constructed terms, as well as display if the boundary
      conditions are met. *)
  val pp_partial_sequent : [< `BdrySat | `BdryUnsat ] -> (Ident.t * tp) list -> (t * tp) Pp.printer

  (** {2 For debugging}
      When debugging, we are not likely to have enough context to use the nice pretty printers above; as a last resort, {!val:dump} and {!val:dump_tp} may be used. *)

  val dump : t Pp.printer
  val dump_tele : tele Pp.printer
  val dump_kan_tele : kan_tele Pp.printer
  val dump_tp : tp Pp.printer
end
