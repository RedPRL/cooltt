open CoolBasis

type info = LexingUtil.span option

let pp_info fmt =
  function
  | None -> Format.fprintf fmt "Unknown location"
  | Some span ->
    LexingUtil.pp_span fmt span


type 'a node =
  {node : 'a;
   info : info}

[@@deriving show]


type cell = Cell of {name : Ident.t; tp : con}
and con = con_ node
and con_ =
  | Var of Ident.t
  | DeBruijnLevel of int
  | Let of con * Ident.t * con
  | Ann of {term : con; tp : con}
  | Nat
  | Suc of con
  | Lit of int
  | Circle
  | Base
  | Loop of con
  | Pi of cell list * con
  | Lam of Ident.t list * con
  | Ap of con * con list
  | Sg of cell list * con
  | Sub of con * con * con
  | Pair of con * con
  | Fst of con
  | Snd of con
  | Type
  | Hole of string option
  | Underscore
  | Unfold of Ident.t list * con
  | Generalize of Ident.t * con
  | Elim of {mot : con; cases : case list; scrut : con}
  | Rec of {mot : con; cases : case list; scrut : con}
  | LamElim of case list
  | Dim
  | Cof
  | CofEq of con * con
  | Join of con list
  | Meet of con list
  | CofBoundary of con
  | Prf of con
  | CofSplit of (con * con) list
  | Ext of Ident.t list * con * (con * con) list
  | Coe of con * con * con * con
  | TopC
  | BotC
  | HCom of con * con * con * con * con
  | HFill of con * con * con * con
  | Com of con * con * con * con * con
  | V of con * con * con * con
  | VProj of con
  | Cap of con
[@@deriving show]

and case = pat * con
[@@deriving show]

and pat = Pat of {lbl : string; args : pat_arg list}
[@@deriving show]

and pat_arg = [`Simple of Ident.t | `Inductive of Ident.t * Ident.t]
[@@deriving show]

type decl =
  | Def of {name : Ident.t; args : cell list; def : con; tp : con}
  | Print of Ident.t node
  | NormalizeTerm of con
  | Quit

type command =
  | NoOp
  | EndOfFile
  | Decl of decl

type signature = decl list
