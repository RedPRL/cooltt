open CoolBasis

type level = [`Info | `Error | `Warn]

type location = LexingUtil.span option

(* We are always using stdout (not stderr) to prevent interleaving *)
val pp_message
  : loc:location
  -> lvl:level
  -> 'a Pp.printer
  -> 'a
  -> unit
