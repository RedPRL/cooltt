type t = [`Anon | `Unqual of string | `Qual of string list * string | `Machine of string]

let pp_modname modparts nm = List.fold_right (fun x acc -> x ^ "." ^ acc) modparts nm

let pp fmt =
  function
  | `Anon -> Format.fprintf fmt "<anon>"
  | `Unqual str -> Uuseg_string.pp_utf_8 fmt str
  | `Qual (modparts, str) -> Uuseg_string.pp_utf_8 fmt (pp_modname modparts str)
  | `Machine str -> Uuseg_string.pp_utf_8 fmt str

let to_string =
  function
  | `Anon -> "<anon>"
  | `Unqual str -> str
  | `Qual (modparts, str) -> pp_modname modparts str
  | `Machine str -> str

let pp_name =
  function
    | `Unqual nm -> Some nm
    | `Qual (modparts, nm) -> Some (pp_modname modparts nm)
    | `Machine nm -> Some nm
    | `Anon -> None
