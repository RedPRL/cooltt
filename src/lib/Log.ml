open Basis

type level = [`Info | `Error | `Warn]

type location = LexingUtil.span option

let pp_lvl fmt =
  function
  | `Info ->
    Format.fprintf fmt "Info"
  | `Error ->
    Format.fprintf fmt "Error"
  | `Warn ->
    Format.fprintf fmt "Warn"

let pp_message ~loc ~lvl ~last_token pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some span ->
    match lvl with
    | `Info ->
      Format.printf "@[<v>%a@]@."
        pp data
    | `Warn ->
      Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
        LexingUtil.pp_span (span,last_token)
        pp_lvl lvl
        pp data
    | `Error ->
      Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
        LexingUtil.pp_span (span,last_token)
        pp_lvl lvl
        pp data
