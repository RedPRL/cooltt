include DomainData

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