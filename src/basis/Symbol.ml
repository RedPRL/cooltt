type t = {gen : int; name : string option}
[@@deriving show]

let global = ref 0

let compare s1 s2 =
  Int.compare s1.gen s2.gen

let equal s1 s2 =
  s1.gen = s2.gen

let named_opt ostr =
  let i = !global in
  let s = {gen = i; name = ostr} in
  global := i + 1;
  s

let named str = named_opt (Some str)
let fresh () = named_opt None

let pp fmt sym =
  match sym.name with
  | Some nm ->
    Format.fprintf fmt "%a" Uuseg_string.pp_utf_8 nm
  | None ->
    Format.fprintf fmt "#%i" sym.gen
