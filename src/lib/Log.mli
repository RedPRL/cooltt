open Basis

type level = [`Info | `Error | `Warn]

type location = DriverError.error_with_maybe_span option

(* We are always using stdout (not stderr) to prevent interleaving *)
val pp_message
  : loc:DriverError.error_with_maybe_span option
  -> lvl:level
  -> last_token:string
  -> 'a Pp.printer
  -> 'a
  -> unit

val pp_runtime_messsage
  : loc:LexingUtil.span option
  -> lvl:level
  -> 'a Pp.printer
  -> 'a
  -> unit
  