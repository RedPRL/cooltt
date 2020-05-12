type t = string

let from_string x = x

let pp fmt x = Uuseg_string.pp_utf_8 fmt x
