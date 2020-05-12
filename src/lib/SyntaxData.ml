open CoolBasis

type t =
  | Var of int
  | Global of Symbol.t
  | Let of t * t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of t * t * t * t
  | Lam of t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
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

  | ElIn of t
  | ElOut of t

  | CodePath of t * t
  | CodePi of t * t
  | CodeSg of t * t
  | CodeNat
  | CodeUniv

and tp =
  | Univ
  | El of t
  | UnfoldEl of t
  | TpVar of int
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of t
  | Sub of tp * t * t
  | Pi of tp * tp
  | Sg of tp * tp
  | Nat

type env = tp list
