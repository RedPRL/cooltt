open CoolBasis.Bwd

type t =
  | Var of int
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
  | Coe of t * t * t * t
  | HCom of t * t * t * t * t
  | Com of t * t * t * t * t
  | SubIn of t
  | SubOut of t
  | Dim0
  | Dim1
  | Cof of (t, t) Cof.cof_f
  | CofSplit of tp * t * t * t * t
  | CofAbort 
  | Prf

  | CodePath of t * t
  | CodePi of t * t
  | CodeSg of t * t
  | CodeNat

and tp = 
  | Univ
  | El of t
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of t 
  | Sub of tp * t * t 
  | Pi of tp * tp
  | Sg of tp * tp 
  | Id of tp * t * t 
  | Nat

and ghost = string bwd * (tp * t) list

type env = tp list
