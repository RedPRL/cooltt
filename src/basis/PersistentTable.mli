(* Due to Conchon & Filliatre *)

(* Redone using Map.Make *)

module type S =
sig
  type key
  type 'a t

  val empty : 'a t
  val size : 'a t -> int
  val get : key -> 'a t -> 'a
  val set : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val remove : key -> 'a t -> 'a t
  val set_opt : key -> 'a option -> 'a t -> 'a t
  val find : key -> 'a t -> 'a option
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** entries from the first argument overwrite the ones from the second. *)
  val merge : 'a t -> 'a t -> 'a t

  val to_list : 'a t -> (key * 'a) list
  val to_list_keys : 'a t -> key list
  val to_list_values : 'a t -> 'a list
end

module type MAKER = functor (O : Map.OrderedType) -> S with type key = O.t

module M : MAKER
