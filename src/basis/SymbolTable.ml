module Vector = CCVector

module type Symbol =
sig
  type t = {gen : int; name : string option}

  val compare : t -> t -> int
  val equal : t -> t -> bool

  val pp : t Pp.printer
  val show : t -> string
end

module type S =
sig
  type 'a t

  (* FIXME: I expose this to make constructing symbols from FQNs easier.
     Find a more modular way of doing this!!
     *)
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
  (* FIXME: Does it ever make sense for this to fail? *)
  val find : symbol -> 'a t -> 'a

  (** Add a batch of symbols to the symbol table.*)
  val append : 'a t -> 'a t -> unit
end

module Make (Sym : Symbol) =
struct
  type symbol = Sym.t

  type 'a t = 'a Vector.vector

  let named_opt nm a syms =
    let gen = Vector.length syms in
    let _ = Vector.push syms a in
    { Sym.gen = gen; name = nm }

  let named nm a syms =
    named_opt (Some nm) a syms

  let empty _ = Vector.create ()

  let length tbl = Vector.length tbl

  let find (sym : Sym.t) syms = Vector.get syms sym.gen

  let append tbl tbl' = Vector.append tbl tbl'
end
