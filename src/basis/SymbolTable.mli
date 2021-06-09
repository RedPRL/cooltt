module type Symbol =
sig
  (** FIXME: Anti-modular *)
  type t = {gen : int; name : string option}

  val compare : t -> t -> int
  val equal : t -> t -> bool

  val pp : t Pp.printer
  val show : t -> string
end

module type S =
sig
  type 'a t

  type symbol

  val empty : unit -> 'a t

  val length : 'a t -> int

  (** Add a binding to the symbol table, and return it's corresponding symbol.
      Note that this is mutable for efficiency reasons.
    *)
  val named : string -> 'a -> 'a t -> symbol

  (** Add a potentially anonymous binding to the symbol table, and return it's corresponding symbol.
      Note that this is mutable for efficiency reasons.
    *)
  val named_opt : string option -> 'a -> 'a t -> symbol

  (** Look up a value in the symbol table. *)
  val find : symbol -> 'a t -> 'a

  (** Add a batch of symbols to the symbol table.*)
  val append : 'a t -> 'a t -> unit
end

module Make (Sym : Symbol) : S with type symbol = Sym.t
