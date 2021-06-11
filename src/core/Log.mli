open Basis

type level = [`Info | `Error | `Warn]

(* We are always using stdout (not stderr) to prevent interleaving *)
val pp_error_message
  : loc:LexingUtil.span option
  -> lvl:level
  -> 'a Pp.printer
  -> 'a
  -> unit

val pp_runtime_message
  : loc:LexingUtil.span option
  -> lvl:level
  -> 'a Pp.printer
  -> 'a
  -> unit
