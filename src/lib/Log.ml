open Basis

type level = [`Info | `Error | `Warn]

type location = DriverError.error_with_maybe_span option

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

let pp_runtime_messsage ~loc ~lvl pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some span ->
    Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
      LexingUtil.pp_span span
      pp_lvl lvl
      pp data


let pp_message ~loc ~lvl ~last_token pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some DriverError.ErrorWithMaybeSpan ( _, None) ->
    pp Format.std_formatter data
  | Some DriverError.ErrorWithMaybeSpan (_, Some span) ->
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
