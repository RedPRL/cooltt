type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


let var v = Var v
let bot = Cof (Join [])
let top = Cof (Meet [])

let eq x y =
  if x = y then top else Cof (Eq (x, y))

let is_syntactic_bot = function Cof (Join []) -> true | _ -> false
let is_syntactic_top = function Cof (Meet []) -> true | _ -> false

let join phis =
  if List.exists is_syntactic_top phis then
    top
  else
    let expose = function Cof (Join phis) -> phis | phi -> [phi] in
    match List.concat_map expose phis with
    | [phi] -> phi
    | l -> Cof (Join l)

let meet phis =
  if List.exists is_syntactic_bot phis then
    bot
  else
    let expose = function Cof (Meet phis) -> phis | phi -> [phi] in
    match List.concat_map expose phis with
    | [phi] -> phi
    | l -> Cof (Meet l)

let boundary ~dim0 ~dim1 r = join [eq r dim0; eq r dim1]

let dump_cof_f dump_r dump_a fmt =
  function
  | Eq (r1, r2) -> Format.fprintf fmt "eq[%a;%a]" dump_r r1 dump_r r2
  | Join l ->
    Format.fprintf fmt "join[%a]"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') dump_a) l
  | Meet l ->
    Format.fprintf fmt "meet[%a]"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') dump_a) l

let rec dump_cof dump_r dump_v fmt =
  function
  | Cof cof -> dump_cof_f dump_r (dump_cof dump_r dump_v) fmt cof
  | Var v -> dump_v fmt v

let pp_cof = dump_cof

let pp_cof_f = dump_cof_f
