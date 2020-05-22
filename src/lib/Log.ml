open CoolBasis

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

let pp_message ~loc ~lvl pp data =
  match loc with
  | None ->
    pp Format.std_formatter data
  | Some span ->
    Format.printf "@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
      LexingUtil.pp_span span
      pp_lvl lvl
      pp data
