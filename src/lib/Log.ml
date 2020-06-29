open Basis

type level = [`Info | `Error | `Warn]

let pp_lvl fmt =
  function
  | `Info ->
    Format.fprintf fmt "Info"
  | `Error ->
    Format.fprintf fmt "Error"
  | `Warn ->
    Format.fprintf fmt "Warn"

let pp_error fmt last_token =
  Format.fprintf fmt "Error near %s" last_token

(*
We have 2 types of messages. Errors from the driver load_file and runtime messages
which may be output or errors.

Error messages either have a span where we can output lots of data about where
the error occured or no span where we just output the data we have avaiable

During Emit, we often don't have a last_token as the parser is happy and we just
have an unbound identifier or a hole. In those cases, we don't print the 
pp_error as it would contain nothing.
*)
let pp_runtime_messsage ~loc ~lvl pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some span ->
    Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
      LexingUtil.pp_span span
      pp_lvl lvl
      pp data


let pp_error_message ~loc ~lvl pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some span ->
    Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
      LexingUtil.pp_span span
      pp_lvl lvl
      pp data
