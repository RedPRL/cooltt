include DomainData
open CoolBasis

let pp_tp fmt _ = 
  Format.fprintf fmt "<tp>"

let pp_con fmt _ = 
  Format.fprintf fmt "<con>"

let push frm (hd, sp) = 
  hd, sp @ [frm]

let mk_var tp lvl = 
  Cut {tp; cut = Var lvl, []; unfold = None}

let dim_to_con =
  function
  | Dim0 -> DimCon0
  | Dim1 -> DimCon1
  | DimVar lvl -> 
    Cut {tp = Tp TpDim; cut = Var lvl, []; unfold = None}
  | DimProbe sym ->
    (* hmmm *)
    Cut {tp = Tp TpDim; cut = Global sym, []; unfold = None}

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
  | _ -> failwith ""