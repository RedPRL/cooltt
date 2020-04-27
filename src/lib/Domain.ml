include DomainData
open CoolBasis

module S = Syntax

let pp_tp fmt =
  function
  | Pi _ ->
    Format.fprintf fmt "<pi>"
  | Sg _ ->
    Format.fprintf fmt "<sg>"
  | Sub _ ->
    Format.fprintf fmt "<sub>"
  | TpPrf _ ->
    Format.fprintf fmt "<prf>"
  | TpCof ->
    Format.fprintf fmt "<cof>"
  | TpDim ->
    Format.fprintf fmt "<dim>"
  | Univ ->
    Format.fprintf fmt "<univ>"
  | Nat ->
    Format.fprintf fmt "<nat>"
  | TpAbort ->
    Format.fprintf fmt "<abort>"
  | El _ ->
    Format.fprintf fmt "<el>"
  | GoalTp _ ->
    Format.fprintf fmt "<goal-tp>"
  | Id _ ->
    Format.fprintf fmt "<id>"


let push frm (hd, sp) =
  hd, sp @ [frm]

let mk_var tp lvl =
  Cut {tp; cut = Var lvl, []; unfold = None}

let const_tm_clo con =
  Clo (S.Var 1, {tpenv = Emp; conenv = Snoc (Emp, con)})
  (* y, x |= y *)

let un_lam con =
  Clo (S.Ap (S.Var 1, S.Var 0), {tpenv = Emp; conenv = Snoc (Emp, con)})
  (* y, x |= y(x) *)

let compose f g =
  Lam (Clo (S.Ap (S.Var 2, S.Ap (S.Var 1, S.Var 0)), {tpenv = Emp; conenv = Snoc (Snoc (Emp, f), g)}))

let apply_to x =
  Clo (S.Ap (S.Var 0, S.Var 1), {tpenv = Emp; conenv = Snoc (Emp, x)})

let fst = Lam (Clo (S.Fst (S.Var 0), {tpenv = Emp; conenv = Emp}))
let snd = Lam (Clo (S.Snd (S.Var 0), {tpenv = Emp; conenv = Emp}))


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

let rec pp_cut : cut Pp.printer =
  fun fmt ->
  function
  | hd, sp ->
    Format.fprintf fmt "%a <: %a"
      pp_hd hd
      pp_sp sp

and pp_hd : hd Pp.printer =
  fun fmt ->
  function
  | Global sym ->
    Format.fprintf fmt "global[%a]" Symbol.pp sym
  | Var lvl ->
    Format.fprintf fmt "var[%i]" lvl
  | Split (tp, phi, psi, clo_phi, clo_psi) ->
    Format.fprintf fmt "[%a => %a | %a => %a]" pp_cof phi pp_clo clo_phi pp_cof psi pp_clo clo_psi
  | SubOut (cut, phi, clo) ->
    Format.fprintf fmt "sub/out[(%a), %a, %a]" pp_cut cut pp_cof phi pp_clo clo
  | _ ->
    Format.fprintf fmt "<hd>"

and pp_sp : frm list Pp.printer =
  fun fmt sp ->
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_frame fmt sp

and pp_frame : frm Pp.printer =
   fun fmt ->
   function
   | KAp _ -> Format.fprintf fmt "<ap>"
   | _ -> Format.fprintf fmt "<frm>"

and pp_cof : cof Pp.printer =
  fun fmt _ ->
  Format.fprintf fmt "<cof>"

and pp_clo : tm_clo Pp.printer =
  fun fmt _ ->
  Format.fprintf fmt "<clo>"

and pp_con : con Pp.printer =
  fun fmt ->
  function
  | Cut {cut} ->
    Format.fprintf fmt "cut[%a]" pp_cut cut
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
