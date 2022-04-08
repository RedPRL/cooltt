module J = Ezjsonm

type t = int

let global = ref 0

let compare p1 p2 = Int.compare p1 p2

let equal p1 p2 = p1 = p2

let pp fmt p =
  Format.fprintf fmt "#%i" p

let show p = Int.to_string p

let serialize (p : t) : J.value =
  `String (Int.to_string p)

let deserialize : J.value -> t =
  function
  | `String p -> int_of_string p
  | j -> J.parse_error j "DimProbe.deserialize"



let fresh () =
  let i = !global in
  global := i + 1;
  i
