type t = [`Anon | `User of string list * string | `Machine of string]

let pp_qual parts nm = String.concat "." (parts @ [nm])

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User (parts, str) -> Uuseg_string.pp_utf_8 fmt (pp_qual parts str)
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str

let to_string =
  function
  | `Anon -> "<anon>"
  | `User (parts, str) -> pp_qual parts str
  | `Machine str -> str

let pp_name =
  function
    | `User (parts, nm) -> Some (pp_qual parts nm)
    | `Machine nm -> Some nm
    | `Anon -> None
