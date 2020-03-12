type t = unit

exception Void

let abort _ = raise Void