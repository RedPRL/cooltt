type t = [`Anon | `User of string list | `Machine of string]
type 'a some = 'a constraint 'a = [< t ]
type user = [ `User of string list ]

let user parts = `User parts

let qual_to_string =
  function
  | [] -> "(root)"
  | parts -> String.concat "." parts

let pp_user fmt =
  function
  | `User parts -> Uuseg_string.pp_utf_8 fmt (qual_to_string parts)

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User _ as u -> pp_user fmt u
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

let user_to_string_opt =
  function
  | `User [] -> None
  | `User parts -> Some (String.concat "." parts)

let equal i0 i1 =
  match (i0, i1) with
  | `User p0, `User p1 -> List.equal String.equal p0 p1
