include DomainData
open CoolBasis

module S = Syntax

let pp_tp fmt _ = 
  Format.fprintf fmt "<tp>"

let push frm (hd, sp) = 
  hd, sp @ [frm]

let mk_var tp lvl = 
  Cut {tp; cut = Var lvl, []; unfold = None}

let const_tm_clo con = 
  Clo (S.Var 1, Snoc (Emp, con)) 
  (* y, x |= y *)

let un_lam con = 
  Clo (S.Ap (S.Var 1, S.Var 0), Snoc (Emp, con))
  (* y, x |= y(x) *)

let compose f g = 
  Lam (Clo (S.Ap (S.Var 2, S.Ap (S.Var 1, S.Var 0)), Snoc (Snoc (Emp, f), g)))

let apply_to x = 
  Clo (S.Ap (S.Var 0, S.Var 1), Snoc (Emp, x))
  
let fst = Lam (Clo (S.Fst (S.Var 0), Emp))
let snd = Lam (Clo (S.Snd (S.Var 0), Emp))


let dim_to_con =
  function
  | Dim0 -> DimCon0
  | Dim1 -> DimCon1
  | DimVar lvl -> 
    Cut {tp = TpDim; cut = Var lvl, []; unfold = None}
  | DimProbe sym ->
    (* hmmm *)
    Cut {tp = TpDim; cut = Global sym, []; unfold = None}

let rec cof_to_con =
  function
  | Cof.Cof (Cof.Eq (r, s)) -> Cof (Cof.Eq (dim_to_con r, dim_to_con s))
  | Cof.Cof Cof.Bot -> Cof Cof.Bot
  | Cof.Cof Cof.Top -> Cof Cof.Top
  | Cof.Cof (Cof.Join (phi0, phi1)) -> Cof (Cof.Join (cof_to_con phi0, cof_to_con phi1))
  | Cof.Cof (Cof.Meet (phi0, phi1)) -> Cof (Cof.Meet (cof_to_con phi0, cof_to_con phi1))
  | Cof.Var lvl -> Cut {tp = TpCof; cut = Var lvl, []; unfold = None}

let rec pp_con : con Pp.printer =
  fun fmt ->
  function
  | Cut _ ->
    Format.fprintf fmt "<cut>"
  | Zero -> 
    Format.fprintf fmt "zero"
  | Suc con -> 
    Format.fprintf fmt "suc[%a]" pp_con con
  | Pair (con0, con1) ->
    Format.fprintf fmt "pair[%a,%a]" pp_con con0 pp_con con1
  | Prf ->
    Format.fprintf fmt "*"
  | Cof _ ->
    Format.fprintf fmt "<cof>"
  | Refl _ ->
    Format.fprintf fmt "refl"
  | GoalRet con ->
    Format.fprintf fmt "goal-ret[%a]" pp_con con
  | Lam clo ->
    Format.fprintf fmt "<lam>"
  | Abort ->
    Format.fprintf fmt "<abort>"
  | _ ->
    Format.fprintf fmt "<don't know how to print>"
