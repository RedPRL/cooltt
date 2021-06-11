type t = [`Anon | `User of string list * string | `Machine of string]

let qual_to_string parts nm = String.concat "." (parts @ [nm])

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User (parts, str) -> Uuseg_string.pp_utf_8 fmt (qual_to_string parts str)
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str

let to_string =
  function
  | `Anon -> "<anon>"
  | `User (parts, str) -> qual_to_string parts str
  | `Machine str -> str

let to_string_opt =
  function
    | `User (parts, nm) -> Some (qual_to_string parts nm)
    | `Machine nm -> Some nm
    | `Anon -> None
