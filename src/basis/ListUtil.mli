val zip : 'a list -> 'b list -> ('a * 'b) list
val unzip : ('a * 'b) list -> 'a list * 'b list
val zip_with : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val map_opt : ('a -> 'b option) -> 'a list -> 'b list option
val map_accum_left : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
