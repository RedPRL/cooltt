type level = [`Info | `Error | `Warn]

type location = (Lexing.position * Lexing.position) option

let pp_lvl fmt =
  function
  | `Info ->
    Format.fprintf fmt "Info"
  | `Error ->
    Format.fprintf fmt "Error"
  | `Warn ->
    Format.fprintf fmt "Warn"

let pp_message ~loc ~lvl pp fmt data =
  match loc with
  | None ->
    pp fmt data
  | Some (start_pos, end_pos) ->
    let open Lexing in
    Format.fprintf fmt "@.@.@[<v>%a:%i.%i-%i.%i [%a]:@,  @[%a@]@]@.@."
      Uuseg_string.pp_utf_8 start_pos.pos_fname
      start_pos.pos_lnum
      (start_pos.pos_cnum - start_pos.pos_bol)
      end_pos.pos_lnum
      (end_pos.pos_cnum - end_pos.pos_bol)
      pp_lvl lvl
      pp data
