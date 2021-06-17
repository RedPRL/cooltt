type t = [`Anon | `User of string list | `Machine of string]

let qual_to_string =
  function
  | [] -> "(root)"
  | parts -> String.concat "." parts

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User parts -> Uuseg_string.pp_utf_8 fmt (qual_to_string parts)
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str

let to_string =
  function
  | `Anon -> "<anon>"
  | `User parts -> qual_to_string parts
  | `Machine str -> str

let to_string_opt =
  function
  | `User parts -> Some (qual_to_string parts)
  | `Machine nm -> Some nm
  | `Anon -> None
