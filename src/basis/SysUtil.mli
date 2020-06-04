exception Not_found

(** portable and reasonable normalization of a mix of absolute and relative paths
    into an absolute path based on chdir/getcwd. *)
val normalize : ?dirs : string list -> string -> string

(** run a {b gyve} and then restore the current cwd. *)
val protect_cwd : (string -> 'a) -> 'a
