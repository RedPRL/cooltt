open Basis

type level = [`Info | `Error | `Warn]

type location = DriverMessage.error option

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

TODO: Cleanly separate errors from runtime output...

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


let pp_error_message ~loc ~lvl ~last_token pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some DriverMessage.DriverError ( _, None) ->
    pp Format.std_formatter data
  | Some DriverMessage.DriverError (_, Some span) ->
    match lvl with
    | `Error ->
      Format.printf "@[<v>%a [%a]:@,  [%a] @[<v>%a@]@]@.@."
        LexingUtil.pp_span span
        pp_lvl lvl
        pp_error last_token
        pp data
    | _ ->
      Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
        LexingUtil.pp_span span
        pp_lvl lvl
        pp data
