type t =
  { origin : string;
    index : int;
    name : string option }
[@@deriving show]

let probe_counter = ref 0

let compare s1 s2 =
  Int.compare s1.index s2.index

let equal s1 s2 =
  s1.index = s2.index

let fresh_probe () =
  let i = !probe_counter in
  let s = {origin = "<dim>"; index = i; name = Some "forall_probe"} in
  probe_counter := i + 1;
  s

let fresh_coe () =
  let i = !probe_counter in
  let s = {origin = "<dim>"; index = i; name = None} in
  probe_counter := i + 1;
  s

let pp fmt sym =
  match sym.name with
  | Some nm ->
    Format.fprintf fmt "%a" Uuseg_string.pp_utf_8 nm
  | None ->
    Format.fprintf fmt "#%i" sym.index
