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
  | GoalRet of t
  | GoalProj of t
  | TpCode of t gtp

and tp = Tp of tp gtp

and _ gtp =
  | Nat : 'a gtp
  | Pi : 'a * 'a -> 'a gtp
  | Sg : tp * tp -> tp gtp
  | Id : tp * t * t -> tp gtp
  | Univ : tp gtp
  | El : t -> tp gtp
  | GoalTp : string option * tp -> tp gtp

and ghost = string bwd * (tp * t) list

type env = tp list

open CoolBasis
val pp : Pp.env -> t Pp.printer
val pp_tp : Pp.env -> tp Pp.printer

val pp_sequent : names:string list -> tp Pp.printer