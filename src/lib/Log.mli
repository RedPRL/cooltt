open CoolBasis

type level = [`Info | `Error | `Warn]

type location = ConcreteSyntax.location

val pp_message
  : loc:location
  -> lvl:level
  -> 'a Pp.printer
  -> Format.formatter
  -> 'a
  -> unit
