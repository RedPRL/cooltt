open Basis

type ddim =
  | DDim0
    (** The left endpoint of the abstract directed interval. *)

  | DDim1
    (** The right endpoint of the abstract directed interval. *)

  | DDimVar of int
  (** In [cooltt], most directed dimension variables are represented as natural
     numbers (pointers into the context). *)

  | DDimSym of Symbol.t
  (** Some directed dimension variables must be generated in a globally
      fresh way ({i e.g.} when computing under a binder). *) (* todo what does this mean *)