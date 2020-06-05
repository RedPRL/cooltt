let debug_mode_flag = ref false

let counter = ref 0
let names = Hashtbl.create 1000

type t = int

let named nm =
  let i = !counter in
  counter := i + 1;
  Hashtbl.add names i nm;
  i

let fresh () =
  named None

let compare =
  Stdlib.compare

let name i =
  match Hashtbl.find names i with
  | Some x -> Some x
  | None -> None

let to_string i =
  match Hashtbl.find names i with
  | Some x -> x
  | None -> "%" ^ string_of_int i

let pp fmt i =
  match Hashtbl.find names i with
  | Some x ->
    begin
      Uuseg_string.pp_utf_8 fmt x;
      if !debug_mode_flag then
        Format.fprintf fmt "%s%i" "%" i
    end
  | None ->
    Format.fprintf fmt "%s%i" "%" i


let set_debug_mode b =
  debug_mode_flag := b
