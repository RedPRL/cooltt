module D := Domain
open CoolBasis 
open Monads

module Error : 
sig
  type t
  val pp : t Pp.printer
end

val equal_con : D.tp -> D.con -> D.con -> [`Ok | `Err of Error.t] quote
val equal_tp : D.tp -> D.tp -> [`Ok | `Err of Error.t] quote