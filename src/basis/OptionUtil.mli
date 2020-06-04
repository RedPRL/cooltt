type 'a t = 'a option
val some : 'a -> 'a option
val map : ('a -> 'b) -> 'a t -> 'b t
val foreach : 'a t -> ('a -> 'b) -> 'b t
val iter : ('a -> unit) -> 'a option -> unit
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val filter_foreach : 'a list -> ('a -> 'b option) -> 'b list
val default : 'a -> 'a option -> 'a
val get_exn : 'a t -> 'a
exception WasNone
