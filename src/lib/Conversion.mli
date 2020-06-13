module D := Domain
open Basis 
open Monads

module Error : 
sig
  type t
  val pp : t Pp.printer
end

val equate_con : D.tp -> D.con -> D.con -> unit conversion
val equate_tp : D.tp -> D.tp -> unit conversion
val trap_err : unit ElabM.m -> [`Ok | `Err of Error.t] ElabM.m
