module D := Domain
open CoolBasis 
open Monads

module Error : 
sig
  type t
  val pp : t Pp.printer
end

val equate_con : D.tp -> D.con -> D.con -> unit quote
val equate_tp : D.tp -> D.tp -> unit quote
val trap_err : unit ElabM.m -> [`Ok | `Err of Error.t] ElabM.m
