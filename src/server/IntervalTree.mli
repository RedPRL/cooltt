(** Interval Trees. *)

type 'a t

val empty : 'a t

(** Insert an element into the tree. *)
val insert : Pos.range -> 'a -> 'a t -> 'a t

(** Construct an interval tree from a list of ranges. *)
val of_list : (Pos.range * 'a) list -> 'a t

(** Lookup a point in the tree, returning the element with the smallest
    interval containing the point *)
val lookup : Pos.t -> 'a t -> 'a option

(** Get all elements that lie contain a provided range. *)
val containing : Pos.range -> 'a t -> 'a list


