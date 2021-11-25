(** Interval Trees. *)

type 'a t

val empty : 'a t

(** Insert an element into the tree. *)
val insert : Pos.t -> Pos.t -> 'a -> 'a t -> 'a t

(** Lookup a point in the tree, returning the element with the smallest
    interval containing the point *)
val lookup : Pos.t -> 'a t -> 'a option

val of_list : (Pos.t * Pos.t * 'a) list -> 'a t
