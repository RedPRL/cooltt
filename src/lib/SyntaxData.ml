open CoolBasis

type t =
  | Var of int
  | Global of Symbol.t
  | Let of t * Ident.t * t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of t * t * t * t
  | Lam of Ident.t * t
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
  | ForallCof of t
  | CofSplit of tp * (t * t) list
  | CofAbort
  | Prf

  | ElIn of t
  | ElOut of t

  | Box of t * t * t * t * t
  | Cap of t * t * t * t * t

  | CodePath of t * t
  | CodePi of t * t
  | CodeSg of t * t
  | CodeNat
  | CodeUniv
  | CodeV of t * t * t * t

and tp =
  | Univ
  | El of t
  | TpVar of int
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of t
  | Sub of tp * t * t
  | Pi of tp * Ident.t * tp
  | Sg of tp * Ident.t * tp
  | Nat

type env = tp list
