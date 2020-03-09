include DomainData

let pp_tp fmt _ = 
  Format.fprintf fmt "<tp>"

let pp_con fmt _ = 
  Format.fprintf fmt "<con>"

let push frm (hd, sp) = 
  hd, sp @ [frm]

let mk_var tp lev = 
  Cut {tp; cut = Var lev, []; unfold = None}