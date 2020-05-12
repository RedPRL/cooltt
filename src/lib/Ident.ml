type t = [`Anon | `User of string | `Machine of string]

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User str -> Uuseg_string.pp_utf_8 fmt str
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str
