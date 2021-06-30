type t = int * int

let nonassoc n = 2*n, 2*n
let left n = 2*n, 2*n+1
let right n = 2*n+1, 2*n
let prefix n = Int.max_int, 2*n
let postfix n = 2*n, Int.max_int

let dual (l, _) (_, r) = l, r

let pp fmt (l, r) = Format.fprintf fmt "<%i-%i>" l r

type env = int * int
let left_of (l, _) = Int.min_int, l
let right_of (_, r) = r, Int.min_int
let surrounded_by (l, r) = r, l
let isolated = Int.min_int, Int.min_int
let isolate_left (_, r) = Int.min_int, r
let isolate_right (l, _) = l, Int.min_int

let pp_env fmt (l,r) =
  match l = Int.min_int, r = Int.min_int with
  | true, true -> Format.fprintf fmt "<none>"
  | false, true -> Format.fprintf fmt "<left:%i>" l
  | true, false -> Format.fprintf fmt "<right:%i>" r
  | false, false -> Format.fprintf fmt "<dual:%i;%i>" l r

let parens (l', r') (l, r) = l' >= l || r' >= r
