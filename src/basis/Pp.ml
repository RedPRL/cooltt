type 'a printer = Format.formatter -> 'a -> unit

open Bwd
open Bwd.Infix

module Env =
struct
  type t = string bwd

  let emp = Emp

  let nat_to_suffix n =
    let formatted = string_of_int n in
    let lookup : int -> string = Array.get [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|] in
    String.concat "" @@
    List.init (String.length formatted) @@
    fun n -> lookup (Char.code (String.get formatted n) - Char.code '0')

  let rec rename xs x i =
    let suffix = nat_to_suffix i in
    let new_x = x ^ suffix in
    if BwdLabels.mem new_x ~set:xs then (rename [@tailcall]) xs x (i + 1) else new_x

  let choose_name (env : t) (x : string) =
    if BwdLabels.mem x ~set:env then rename env x 1 else x

  let var i env =
    match BwdLabels.nth_opt env i with
    | Some v -> v
    | None -> failwith "Pp printer: tried to resolve bound variable out of range"

  let proj xs =
    match xs with
    | Emp -> failwith "ppenv/proj"
    | Snoc (xs, _) -> xs

  let bind (env : t) (nm : string option) : string * t =
    let x =
      match nm with
      | None -> choose_name env "_x"
      | Some x -> choose_name env x
    in
    x, env #< x

  let bind_underscore (env : t) : string * t =
    "_", env #< "_"

  let rec bindn (env : t) (nms : string option list) : string list * t =
    match nms with
    | [] ->
      [], env
    | nm :: nms ->
      let x, env' = bind env nm in
      let xs, env'' = bindn env' nms in
      (x :: xs), env''

  let names (env : t) : string list =
    env <>> []
end

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

type env = Env.t
