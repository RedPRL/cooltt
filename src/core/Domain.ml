include DomainData
open Basis
open Bwd

module Make (Symbol : Symbol.S) =
struct
  include DomainData.Make(Symbol)
  module S = Syntax.Make(Symbol)

  let const_tp_clo tp =
    Clo (S.TpVar 0, {tpenv = Snoc (Emp, tp); conenv = Emp})

  let const_tm_clo con =
    Clo (S.Var 0, {tpenv = Emp; conenv = Snoc (Emp, con)})

  let push frm (hd, sp) =
    hd, sp @ [frm]

  let mk_var tp lvl =
    Cut {tp; cut = Var lvl, []}

  let un_lam con =
    (* y, x |= y(x) *)
    Clo (S.Ap (S.Var 1, S.Var 0), {tpenv = Emp; conenv = Snoc (Emp, con)})

  let compose f g =
    Lam (`Anon, Clo (S.Ap (S.Var 2, S.Ap (S.Var 1, S.Var 0)), {tpenv = Emp; conenv = Snoc (Snoc (Emp, f), g)}))

  let apply_to x =
    Clo (S.Ap (S.Var 0, S.Var 1), {tpenv = Emp; conenv = Snoc (Emp, x)})

  let fst = Lam (`Anon, Clo (S.Fst (S.Var 0), {tpenv = Emp; conenv = Emp}))
  let snd = Lam (`Anon, Clo (S.Snd (S.Var 0), {tpenv = Emp; conenv = Emp}))

  let proj lbl = Lam (`Anon, Clo (S.Proj (S.Var 0, lbl), {tpenv = Emp; conenv = Emp}))
  let el_out = Lam (`Anon, Clo (S.ElOut (S.Var 0), {tpenv = Emp; conenv = Emp}))

  let tm_abort = Split []
  let tp_abort = TpSplit []

  let sign_lbls =
    function
    | Field (lbl, _, Clo (sign, _)) -> lbl :: (List.map (fun (lbl, _) -> lbl) sign)
    | Empty -> []

  let dim_to_con =
    function
    | Dim.Dim0 -> Dim0
    | Dim.Dim1 -> Dim1
    | Dim.DimVar (CofVar.Local lvl) ->
      Cut {tp = TpDim; cut = Var lvl, []}
    | Dim.DimVar (CofVar.Axiom sym) ->
      Cut {tp = TpDim; cut = Global sym, []}
    | Dim.DimProbe sym ->
      DimProbe sym

  let rec cof_to_con =
    let module K = Kado.Syntax in
    function
    | K.Cof (S.Cof.Eq (r, s)) -> Cof (K.Eq (dim_to_con r, dim_to_con s))
    | K.Cof (S.Cof.Join phis) -> Cof (K.Join (List.map cof_to_con phis))
    | K.Cof (S.Cof.Meet phis) -> Cof (K.Meet (List.map cof_to_con phis))
    | K.Var (CofVar.Local lvl) -> Cut {tp = TpCof; cut = Var lvl, []}
    | K.Var (CofVar.Axiom sym) -> Cut {tp = TpCof; cut = Global sym, []}

  let pp_lsq fmt () = Format.fprintf fmt "["
  let pp_rsq fmt () = Format.fprintf fmt "]"

  let pp_list_group ~left ~right ~sep pp fmt xs =
    Format.fprintf fmt "@[<hv0>%a %a@ %a@]"
      left ()
      (Format.pp_print_list ~pp_sep:sep pp) xs
      right ()

  let rec pp_cut : cut Pp.printer =
    fun fmt ->
    function
    | hd, sp ->
      Format.fprintf fmt "%a <: %a"
        pp_hd hd
        pp_spine sp

  and pp_split_branch fmt (phi, clo_phi) =
    Format.fprintf fmt "@[<hv>%a =>@ %a@]" pp_cof phi pp_clo clo_phi

  and pp_hd : hd Pp.printer =
    fun fmt ->
    function
    | Global sym ->
      Format.fprintf fmt "global[%a]" Symbol.pp sym
    | Var lvl ->
      Format.fprintf fmt "var[%i]" lvl
    | UnstableCut _ ->
      Format.fprintf fmt "<unstable>"
    | Coe _ ->
      Format.fprintf fmt "<coe>"

  and pp_spine : frm list Pp.printer =
    fun fmt sp ->
    let comma fmt () = Format.fprintf fmt ", " in
    Format.pp_print_list ~pp_sep:comma pp_frame fmt sp

  and pp_frame : frm Pp.printer =
    fun fmt ->
    function
    | KAp (_, con) -> Format.fprintf fmt "ap[%a]" pp_con con
    | KFst -> Format.fprintf fmt "fst"
    | KSnd -> Format.fprintf fmt "snd"
    | KProj lbl -> Format.fprintf fmt "proj[%a]" Ident.pp_user lbl
    | KNatElim _ -> Format.fprintf fmt "<nat-elim>"
    | KCircleElim _ -> Format.fprintf fmt "<circle-elim>"
    | KElOut -> Uuseg_string.pp_utf_8 fmt "⭝ₑₗ"

  and pp_cof : cof Pp.printer =
    fun fmt cof ->
    pp_con fmt (cof_to_con cof)

  and pp_dim : dim Pp.printer =
    fun fmt r ->
    pp_con fmt @@ dim_to_con r

  and pp_clo : tm_clo Pp.printer =
    let sep fmt () = Format.fprintf fmt "," in
    fun fmt (Clo (tm, {tpenv; conenv})) ->
      Format.fprintf fmt "clo[%a ; [%a ; %a]]"
        S.dump tm
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_tp) (BwdLabels.to_list tpenv)
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_con) (BwdLabels.to_list conenv)

  and pp_tp_clo : tp_clo Pp.printer =
    let sep fmt () = Format.fprintf fmt "," in
    fun fmt (Clo (tp, {tpenv; conenv})) ->
      Format.fprintf fmt "tpclo[%a ; [%a ; %a]]"
        S.dump_tp tp
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_tp) (BwdLabels.to_list tpenv)
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_con) (BwdLabels.to_list conenv)

  and pp_sign_clo : (S.sign clo) Pp.printer =
    let sep fmt () = Format.fprintf fmt "," in
    fun fmt (Clo (sign, {tpenv; conenv})) ->
      Format.fprintf fmt "tpclo[%a ; [%a ; %a]]"
        S.dump_sign sign
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_tp) (BwdLabels.to_list tpenv)
        (pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep pp_con) (BwdLabels.to_list conenv)

  and pp_con : con Pp.printer =
    fun fmt ->
    function
    | Cut {cut;tp} ->
      Format.fprintf fmt "cut[%a :: %a]" pp_cut cut pp_tp tp
    | Zero ->
      Format.fprintf fmt "zero"
    | Suc con ->
      Format.fprintf fmt "suc[%a]" pp_con con
    | Base ->
      Format.fprintf fmt "base"
    | Loop r ->
      Format.fprintf fmt "loop[%a]" pp_dim r
    | Pair (con0, con1) ->
      Format.fprintf fmt "pair[%a,%a]" pp_con con0 pp_con con1
    | Struct fields ->
      Format.fprintf fmt "struct[%a]"
        (Pp.pp_sep_list (fun fmt (lbl, tp) -> Format.fprintf fmt "%a : %a" Ident.pp_user lbl pp_con tp)) fields
    | Prf ->
      Format.fprintf fmt "*"
    | Cof (Eq (x, y)) ->
      Format.fprintf fmt "eq[%a,%a]" pp_con x pp_con y
    | Cof (Join phis) ->
      Format.fprintf fmt "join[%a]" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") pp_con) phis
    | Cof (Meet phis) ->
      Format.fprintf fmt "meet[%a]" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") pp_con) phis
    | DimProbe x ->
      Format.fprintf fmt "probe[%a]" DimProbe.pp x
    | Lam (_, clo) ->
      Format.fprintf fmt "lam[%a]" pp_clo clo
    | Dim0 ->
      Format.fprintf fmt "dim0"
    | Dim1 ->
      Format.fprintf fmt "dim1"
    | ElIn con ->
      Format.fprintf fmt "el/in[%a]" pp_con con
    | StableCode `Nat ->
      Format.fprintf fmt "nat/code"
    | StableCode `Circle ->
      Format.fprintf fmt "circle/code"
    | SubIn _ ->
      Format.fprintf fmt "<sub/in>"
    | FHCom _ ->
      Format.fprintf fmt "<fhcom>"
    | LetSym _ ->
      Format.fprintf fmt "<let-sym>"
    | StableCode `Univ -> Format.fprintf fmt "<code-univ>"
    | BindSym _ -> Format.fprintf fmt "<bind-sym>"
    | StableCode code -> pp_stable_code fmt code
    | UnstableCode _ -> Format.fprintf fmt "<unstable-code>"
    | Box _ -> Format.fprintf fmt "<box>"
    | VIn _ -> Format.fprintf fmt "<vin>"
    | Split branches ->
      let sep fmt () = Format.fprintf fmt "@ | " in
      pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep
        pp_split_branch
        fmt
        branches
    | LockedPrfIn _ ->
      Format.fprintf fmt "<wrap>"


  and pp_sign fmt =
    function
    | Field (ident, tp, clo) -> Format.fprintf fmt "sig/field[%a,%a,%a]" Ident.pp_user ident pp_tp tp pp_sign_clo clo
    | Empty -> Format.fprintf fmt "sig/empty"

  and pp_tp fmt =
    function
    | Pi (base, ident, fam) ->
      Format.fprintf fmt "pi[%a,%a,%a]" pp_tp base Ident.pp ident pp_tp_clo fam
    | Sg _ ->
      Format.fprintf fmt "<sg>"
    | Signature sign ->
      Format.fprintf fmt "sig[%a]" pp_sign sign
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
    | Circle ->
      Format.fprintf fmt "<circle>"
    | ElStable code ->
      Format.fprintf fmt "el[%a]" pp_stable_code code
    | ElCut con ->
      Format.fprintf fmt "el-cut[%a]" pp_cut con
    | ElUnstable (`HCom _) ->
      Format.fprintf fmt "<Hcom>"
    | ElUnstable (`V _) ->
      Format.fprintf fmt "<V>"
    | TpSplit _ ->
      Format.fprintf fmt "<split>"
    | TpLockedPrf _ ->
      Format.fprintf fmt "<wrap>"

  and pp_stable_code fmt =
    function
    | `Ext _ -> Format.fprintf fmt "<code-ext>"
    | `Pi _ -> Format.fprintf fmt "<code-pi>"
    | `Sg _ -> Format.fprintf fmt "<code-sg>"
    | `Signature _ -> Format.fprintf fmt "<code-sig>"
    | `Nat -> Format.fprintf fmt "<code-nat>"
    | `Circle -> Format.fprintf fmt "<code-circle>"
    | `Univ -> Format.fprintf fmt "<code-univ>"

end
