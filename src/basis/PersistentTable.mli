(* Due to Conchon & Filliatre *)

module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val size : ('k, 'a) t -> int
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t
  val mem : 'k -> ('k, 'a) t -> bool
  val remove : 'k -> ('k, 'a) t -> ('k, 'a) t
  val set_opt : 'k -> 'a option -> ('k, 'a) t -> ('k, 'a) t
  val find : 'k -> ('k, 'a) t -> 'a option
  val fold : ('k -> 'a -> 'b -> 'b) -> ('k, 'a) t -> 'b -> 'b

  (** entries from the first argument overwrite the ones from the second. *)
  val merge : ('k, 'a) t -> ('k, 'a) t -> ('k, 'a) t

  val to_list : ('k, 'a) t -> ('k * 'a) list
  val to_list_keys : ('k, 'a) t -> 'k list
  val to_list_values : ('k, 'a) t -> 'a list
end

module M : S
