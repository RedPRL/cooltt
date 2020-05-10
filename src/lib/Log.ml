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

let pp_message ~loc ~lvl pp fmt data =
  match loc with
  | None ->
    pp fmt data
  | Some span ->
    Format.fprintf fmt "@.@.@[<v>%a [%a]:@,  @[<v>%a@]@]@.@."
      LexingUtil.pp_span span
      pp_lvl lvl
      pp data
