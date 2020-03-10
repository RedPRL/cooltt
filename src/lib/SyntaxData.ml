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
  | HCom of t * t * t * cof * t
  | TpCode of t gtp
  | CofTree of cof_tree
  | SubIn of t
  | SubOut of t
  | Dim0
  | Dim1
  | Cof of (t, t) Cof.cof

and cof = (int, t) Cof.cof
and cof_tree = (int, t, t) Cof.tree

and tp = Tp of tp gtp

and _ gtp =
  | Nat : 'a gtp
  | Pi : 'a * 'a -> 'a gtp
  | Sg : 'a * 'a -> 'a gtp
  | Id : 'a * t * t -> 'a gtp
  | Sub : 'a * cof * t -> 'a gtp
  | Univ : tp gtp
  | El : t -> tp gtp
  | GoalTp : string option * tp -> tp gtp
  | TpDim : tp gtp
  | TpCof : tp gtp
  | TpPrf : cof -> tp gtp


and ghost = string bwd * (tp * t) list

type env = tp list