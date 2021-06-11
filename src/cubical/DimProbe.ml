type t = int

let global = ref 0

let compare p1 p2 = Int.compare p1 p2

let equal p1 p2 = p1 = p2

let pp fmt p =
  Format.fprintf fmt "#%i" p

let show p = Int.to_string p

let fresh () =
  let i = !global in
  global := i + 1;
  i
