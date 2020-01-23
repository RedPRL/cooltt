open CoolBasis.Bwd

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Global of Symbol.t
  | Let of t * t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of ghost option * tp * t * t * t
  | Lam of t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of ghost option * tp * t * t
  | CodeNat
  | CodePi of t * t
  | GoalRet of t
  | GoalProj of t

and tp =
  | Nat
  | Pi of tp * tp
  | Sg of tp * tp
  | Id of tp * t * t
  | Univ
  | El of t
  | GoalTp of string option * tp

and ghost = string bwd * (tp * t) list

type env = tp list

open CoolBasis
val pp : t Pp.printer 
val pp_tp : tp Pp.printer 

val pp_ : Pp.env -> t Pp.printer
val pp_tp_ : Pp.env -> tp Pp.printer

val pp_sequent : names:string list -> tp Pp.printer