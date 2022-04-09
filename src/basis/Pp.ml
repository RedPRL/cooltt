type 'a printer = Format.formatter -> 'a -> unit

open Bwd
open BwdNotation

module Env =
struct
  type t = int * string bwd

  let emp = 0, Emp

  let nat_to_suffix n =
    let formatted = string_of_int n in
    let lookup : int -> string = List.nth ["₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"] in
    String.concat "" @@
    List.init (String.length formatted) @@
    fun n -> lookup (Char.code (String.get formatted n) - Char.code '0')

  let rec rename xs x i =
    let suffix = nat_to_suffix i in
    let new_x = x ^ suffix in
    if BwdLabels.mem new_x ~set:xs then (rename [@tailcall]) xs x (i + 1) else new_x

  let choose_name (env : t) (x : string) =
    if BwdLabels.mem x ~set:(snd env) then rename (snd env) x 1 else x

  let var i env =
    if i < fst env then
      BwdLabels.nth (snd env) i
    else
      failwith "Pp printer: tried to resolve bound variable out of range"

  let proj xs =
    match xs with
    | _, Emp -> failwith "ppenv/proj"
    | n, Snoc (xs, _) -> n-1, xs

  let bind (env : t) (nm : string option) : string * t =
    let x =
      match nm with
      | None -> choose_name env "_x"
      | Some x -> choose_name env x
    in
    x, (fst env + 1, ((snd env) #< x))

  let rec bindn (env : t) (nms : string option list) : string list * t =
    match nms with
    | [] ->
      [], env
    | nm :: nms ->
      let x, env' = bind env nm in
      let xs, env'' = bindn env' nms in
      (x :: xs), env''

  let names (env : t) : string list =
    snd env <>> []
end

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

type env = Env.t
