open CoolBasis.Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int

type cof = (int, dim) Cof.cof

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
  | DimLam of t
  | DimAp of t * dim
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of ghost option * tp * t * t
  | GoalRet of t
  | GoalProj of t
  | Coe of t * dim * dim * t
  | HCom of t * dim * dim * cof * t
  | TpCode of t gtp
  | CofTree of cof_tree
  | SubIn of t
  | SubOut of t

and cof_tree = (int, dim, t) Cof.tree

and tp = Tp of tp gtp

and _ gtp =
  | Nat : 'a gtp
  | Pi : 'a * 'a -> 'a gtp
  | Sg : 'a * 'a -> 'a gtp
  | Id : 'a * t * t -> 'a gtp
  | DimPi : 'a -> 'a gtp
  | Sub : 'a * cof * t -> 'a gtp
  | Univ : tp gtp
  | El : t -> tp gtp
  | GoalTp : string option * tp -> tp gtp

and ghost = string bwd * [`Con of (tp * t) | `Dim of dim | `Cof of cof] list

type env = tp list