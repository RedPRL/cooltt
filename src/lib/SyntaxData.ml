type t =
  | Var of int
  | Global of Symbol.t
  | Let of t * t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of tp * t * t * t
  | Lam of t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of tp * t * t
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

  | CodePath of t * t (* todo/iev: is this going to be deprecated? or was it kind of done in advance?*)
  | CodePi of t * t
  | CodeSg of t * t
  | CodeNat

  | PathLam of t * t (*todo/iev: this is very certainly a bad name, but i need an intro form to match Carlo's <x>M *)
  | PathAp of t * t (* todo/iev: my thought here is to match Carlo's iapp form, as in the elim rule for paths *)

and tp =
  | Univ
  | El of t
  | TpVar of int
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of t
  | Sub of tp * t * t
  | Pi of tp * tp
  | Sg of tp * tp
  | Id of tp * t * t
  | Nat
  | Path of tp * t * t (*todo/iev: not quite sure i really understand why this should be in tp not t, given the relative flatness of coresyntaxdata.t*)

type env = tp list
