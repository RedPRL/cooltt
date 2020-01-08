type 'a printer = Format.formatter -> 'a -> unit

open Bwd 
open BwdNotation

module Env =
struct
  type t = string bwd

  let emp = Emp

  let var i xs =
    if i < Bwd.length xs then
      Bwd.nth xs i
    else
      failwith "Pp printer: tried to resolve bound variable out of range"

  let proj xs =
    match xs with
    | Emp -> failwith "ppenv/proj"
    | Snoc (xs, _) -> xs

  let nat_to_suffix n =
    let formatted = string_of_int n in
    let lookup : int -> string = List.nth ["₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"] in
    String.concat "" @@
    List.init (String.length formatted) @@
    fun n -> lookup (Char.code (String.get formatted n) - Char.code '0')

  let rec rename xs x i =
    let suffix = nat_to_suffix i in
    let new_x = x ^ suffix in
    if Bwd.mem new_x xs then (rename [@tailcall]) xs x (i + 1) else new_x

  let choose_name xs x =
    if Bwd.mem x xs then rename xs x 1 else x

  let bind xs nm =
    let x =
      match nm with
      | None | Some "_" -> choose_name xs "x"
      | Some x -> choose_name xs x
    in
    x, xs #< x

  let rec bindn env (nms : string option list) =
    match nms with
    | [] ->
      [], env
    | nm :: nms ->
      let x, env' = bind env nm in
      let xs, env'' = bindn env' nms in
      (x :: xs), env''
end

type env = Env.t