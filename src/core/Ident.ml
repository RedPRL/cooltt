type t = [`Anon | `User of string list | `Machine of string | `Unfolder of t | `Blocked of t list]
type 'a some = 'a constraint 'a = [< t ]
type user = [ `User of string list ]

module J = Ezjsonm


let user parts = `User parts
let machine str = `Machine str
let unfolder i = `Unfolder i
let anon = `Anon
let blocked ts = `Blocked ts

let qual_to_string =
  function
  | [] -> "∷"
  | parts -> String.concat "∷" parts

let pp_user fmt =
  function
  | `User parts -> Uuseg_string.pp_utf_8 fmt (qual_to_string parts)

let rec pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `User _ as u -> pp_user fmt u
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str
  | `Unfolder t -> Format.fprintf fmt "unfold[%a]" pp t
  | `Blocked ts ->
    let comma fmt () = Format.fprintf fmt "," in
    Format.fprintf fmt "blocked[%a]" (Format.pp_print_list ~pp_sep:comma pp) ts

let to_string i =
  let _ = Format.flush_str_formatter () in 
  Format.fprintf Format.str_formatter "%a" pp i ;
  Format.flush_str_formatter ()

let to_string_opt : t -> string option =
  function
  | `Anon -> None 
  | i -> Some (to_string i)

let user_to_string_opt =
  function
  | `User [] -> None
  | `User parts -> Some (String.concat "∷" parts)

let json_of_user : [`User of string list ] -> [> `A of J.value list ] =
  function
  | `User path -> `A (List.map J.string path)

let json_to_user : J.value -> [> `User of string list] =
  function
  | `A path -> `User (List.map J.get_string path)
  | j -> J.parse_error j "json_to_path"


let rec json_of_ident : t -> J.value =
  function
  | `Anon -> `String "anon"
  | `User _ as u -> `O [("user", json_of_user u)]
  | `Machine str -> `O [("machine", `String str)]
  | `Unfolder i -> `O [("unfolder", json_of_ident i)]
  | `Blocked ts -> `O [("blocked", J.list json_of_ident ts)]

let rec json_to_ident : J.value -> t =
  function
  | `String "anon" -> `Anon
  | `O [("user", parts)] -> json_to_user parts
  | `O [("machine", `String str)] -> machine str
  | `O [("unfolder", i)] -> unfolder @@ json_to_ident i
  | `O [("blocked", ts)] -> blocked @@ J.get_list json_to_ident ts
  | j -> J.parse_error j "json_to_ident"

let equal i0 i1 =
  match (i0, i1) with
  | `User p0, `User p1 -> List.equal String.equal p0 p1
