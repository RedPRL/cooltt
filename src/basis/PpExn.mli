exception Unrecognized

type printer = Format.formatter -> exn -> unit
val pp : printer

val install_printer : printer -> unit