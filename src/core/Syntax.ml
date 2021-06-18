open Basis
open Bwd
open Cubical

module Make (Symbol : Symbol.S) =
struct
  include SyntaxData.Make (Symbol)

  let debug_mode = false

  let rec to_numeral =
    function
    | Zero -> Some 0
    | Suc t ->
      Option.map (fun n -> n + 1) @@
      to_numeral t
    | _ -> None

  let tm_abort = CofSplit []
  let tp_abort = TpCofSplit []

  module Fmt = Format

  let rec dump fmt =
    function
    | Var i -> Format.fprintf fmt "var[%i]" i
    | Global _ -> Format.fprintf fmt "<global>"
    | Let _ -> Format.fprintf fmt "<let>"
    | Ann _ -> Format.fprintf fmt "<ann>"

    | Zero -> Format.fprintf fmt "zero"
    | Suc tm -> Format.fprintf fmt "suc[%a]" dump tm
    | NatElim _ -> Format.fprintf fmt "<nat-elam>"

    | Base -> Format.fprintf fmt "base"
    | Loop _ -> Format.fprintf fmt "<loop>"
    | CircleElim _ -> Format.fprintf fmt "<circle/elim>"

    | Lam (ident, tm) -> Format.fprintf fmt "lam[%a, %a]" Ident.pp ident dump tm
    | Ap (tm0, tm1) -> Format.fprintf fmt "ap[%a, %a]" dump tm0 dump tm1

    | Pair (tm0, tm1) -> Format.fprintf fmt "pair[%a, %a]" dump tm0 dump tm1
    | Fst tm -> Format.fprintf fmt "fst[%a]" dump tm
    | Snd tm -> Format.fprintf fmt "snd[%a]" dump tm

    | Coe _ -> Format.fprintf fmt "<coe>"
    | HCom _ -> Format.fprintf fmt "<hcom>"
    | Com _ -> Format.fprintf fmt "<com>"

    | SubIn _ -> Format.fprintf fmt "<sub/in>"
    | SubOut _ -> Format.fprintf fmt "<sub/out>"

    | Dim0 -> Format.fprintf fmt "<dim0>"
    | Dim1 -> Format.fprintf fmt "<dim1>"
    | Cof cof -> Format.fprintf fmt "cof[%a]" dump_cof cof
    | ForallCof _ -> Format.fprintf fmt "<dim1>"
    | CofSplit branches -> Format.fprintf fmt "cof/split[%a]" (Pp.pp_sep_list dump_branch) branches
    | Prf -> Format.fprintf fmt "prf"

    | ElIn tm -> Format.fprintf fmt "el/in[%a]" dump tm
    | ElOut tm -> Format.fprintf fmt "el/out[%a]" dump tm

    | Box _ -> Format.fprintf fmt "<box>"
    | Cap _ -> Format.fprintf fmt "<cap>"

    | VIn _ -> Format.fprintf fmt "<vin>"
    | VProj _ -> Format.fprintf fmt "<vproj>"

    | CodeExt _ -> Format.fprintf fmt "<ext>"
    | CodePi _ -> Format.fprintf fmt "<pi>"
    | CodeSg _ -> Format.fprintf fmt "<sg>"
    | CodeRecord fields -> Format.fprintf fmt "record[%a]" (Pp.pp_sep_list (fun fmt (nm, tp) -> Format.fprintf fmt "%a : %a" Ident.pp nm dump tp)) fields
    | CodeNat -> Format.fprintf fmt "nat"
    | CodeUniv -> Format.fprintf fmt "univ"
    | CodeV _ -> Format.fprintf fmt "<v>"
    | CodeCircle -> Format.fprintf fmt "circle"

    | ESub _ -> Format.fprintf fmt "<esub>"

    | LockedPrfIn _ -> Format.fprintf fmt "<locked/in>"
    | LockedPrfUnlock _ -> Format.fprintf fmt "<locked/unlock>"

  and dump_tp fmt =
    function
    | Univ -> Format.fprintf fmt "univ"
    | El t -> Format.fprintf fmt "el[%a]" dump t
    | TpVar i -> Format.fprintf fmt "tp/var[%i]" i
    | TpDim -> Format.fprintf fmt "tp/dim"
    | TpCof -> Format.fprintf fmt "tp/cof"
    | TpPrf t -> Format.fprintf fmt "tp/prf[%a]" dump t
    | TpCofSplit _ -> Format.fprintf fmt "<tp/cof/split>"
    | Sub _ -> Format.fprintf fmt "<sub>"
    | Pi (base, ident, fam) -> Format.fprintf fmt "pi[%a, %a, %a]" dump_tp base Ident.pp ident dump_tp fam
    | Sg _ -> Format.fprintf fmt "<sg>"
    | Record fields -> Format.fprintf fmt "tp/record[%a]" (Pp.pp_sep_list (fun fmt (nm, tp) -> Format.fprintf fmt "%a : %a" Ident.pp nm dump_tp tp)) fields
    | Nat -> Format.fprintf fmt "nat"
    | Circle -> Format.fprintf fmt "circle"
    | TpESub _ -> Format.fprintf fmt "<esub>"
    | TpLockedPrf _ -> Format.fprintf fmt "<locked>"


  and dump_cof fmt =
    function
    | Cof.Eq (r1, r2) -> Format.fprintf fmt "eq[%a, %a]" dump r1 dump r2
    | Cof.Join cofs -> Format.fprintf fmt "join[%a]" (Pp.pp_sep_list dump) cofs
    | Cof.Meet cofs -> Format.fprintf fmt "meet[%a]" (Pp.pp_sep_list dump) cofs

  and dump_branch fmt (cof, bdy) =
    Format.fprintf fmt "[%a, %a]" dump cof dump bdy


  let pp_var env fmt ix =
    Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var ix env

  and pp_problem fmt problem =
    let lbls = Bwd.to_list problem in
    let dot fmt () = Fmt.fprintf fmt "." in
    Fmt.pp_print_list ~pp_sep:dot Uuseg_string.pp_utf_8 fmt lbls


  let pp_lsq fmt () = Format.fprintf fmt "["
  let pp_rsq fmt () = Format.fprintf fmt "]"

  let pp_list_group ~left ~right ~sep pp fmt xs =
    Format.fprintf fmt "@[<hv0>%a %a@ %a@]"
      left ()
      (Format.pp_print_list ~pp_sep:sep pp) xs
      right ()

  let pp_tuple =
    let sep fmt () = Format.fprintf fmt "@ , " in
    pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep

  let pp_braced pp fmt a =
    Format.fprintf fmt "{%a}"
      pp a

  let ppenv_bind env ident =
    Pp.Env.bind env @@ Ident.to_string_opt ident

  let rec pp_fields env pp_field fmt  =
    function
    | [] -> Format.fprintf fmt ""
    | ((ident, tp) :: fields) ->
       let x, envx = ppenv_bind env ident in
       Format.fprintf fmt "(%a : %a) %a" Uuseg_string.pp_utf_8 x (pp_field env) tp (pp_fields envx pp_field) fields

  let rec pp env fmt tm =
    match tm with
    | Lam _ ->
      Format.fprintf fmt "@[%a@]"
        (pp_lambdas env) tm
    | Ap _ ->
      pp_applications env fmt tm
    | Pair (tm0, tm1) ->
      pp_tuple (pp env) fmt [tm0; tm1]
    | CofSplit branches ->
      let sep fmt () = Format.fprintf fmt "@ | " in
      pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep
        (pp_cof_split_branch env)
        fmt
        branches
    | HCom (code, r, s, phi, bdy) ->
      Format.fprintf fmt "@[<hv2>hcom %a %a %a %a@ %a@]"
        (pp_atomic env) code
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) phi
        (pp_atomic env) bdy
    | Com (fam, r, s, phi, bdy) ->
      Format.fprintf fmt "@[<hv2>com %a %a %a %a@ %a@]"
        (pp_atomic env) fam
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) phi
        (pp_atomic env) bdy
    | Coe (fam, r, s, bdy) ->
      Format.fprintf fmt "@[<hv2>coe %a %a %a@ %a@]"
        (pp_atomic env) fam
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) bdy
    | Var ix ->
      pp_var env fmt ix
    | Global sym ->
      Symbol.pp fmt sym
    | Cof (Cof.Eq (r, s)) ->
      Format.fprintf fmt "%a = %a" (pp_atomic env) r (pp_atomic env) s
    | Cof (Cof.Join []) ->
      Format.fprintf fmt "#f"
    | Cof (Cof.Join phis) ->
      Format.pp_print_list ~pp_sep:(fun fmt () -> Uuseg_string.pp_utf_8 fmt " ∨ ") (pp_atomic env) fmt phis
    | Cof (Cof.Meet []) ->
      Format.fprintf fmt "#t"
    | Cof (Cof.Meet phis) ->
      Format.pp_print_list ~pp_sep:(fun fmt () -> Uuseg_string.pp_utf_8 fmt " ∧ ") (pp_atomic env) fmt phis
    | ForallCof phi ->
      let x, envx = ppenv_bind env `Anon in
      Format.fprintf fmt "%a %a %a %a"
        Uuseg_string.pp_utf_8 "∀"
        Uuseg_string.pp_utf_8 x
        Uuseg_string.pp_utf_8 "→"
        (pp envx) phi
    | Fst tm ->
      Format.fprintf fmt "fst %a" (pp_atomic env) tm
    | Snd tm ->
      Format.fprintf fmt "snd %a" (pp_atomic env) tm
    | Zero ->
      Format.fprintf fmt "0"
    | Suc tm ->
      begin
        match to_numeral tm with
        | Some n -> Format.fprintf fmt "%i" (n + 1)
        | None -> Format.fprintf fmt "suc %a" (pp_atomic env) tm
      end
    | NatElim (mot, zero, suc, tm) ->
      Format.fprintf fmt "@[<hv2>elim %a %s %a@ @[<v>[ zero => %a@ | suc => %a@ ]@]@]"
        (pp_atomic env) tm
        "@"
        (pp_atomic env) mot
        (pp env) zero
        (pp env) suc
    | Base ->
      Format.fprintf fmt "base"
    | Loop tm ->
      Format.fprintf fmt "loop %a" (pp_atomic env) tm
    | CircleElim (mot, base, loop, tm) ->
      Format.fprintf fmt "@[<hv2>elim %a %s %a@ @[<v>[ base => %a@ | loop => %a@ ]@]@]"
        (pp_atomic env) tm
        "@"
        (pp_atomic env) mot
        (pp env) base
        (pp env) loop
    | SubIn tm when debug_mode ->
      Format.fprintf fmt "sub/in %a" (pp_atomic env) tm
    | SubOut tm when debug_mode ->
      Format.fprintf fmt "sub/out %a" (pp_atomic env) tm
    | ElIn tm when debug_mode ->
      Format.fprintf fmt "el/in %a" (pp_atomic env) tm
    | ElOut tm when debug_mode ->
      Format.fprintf fmt "el/out %a" (pp_atomic env) tm
    | SubIn tm | SubOut tm | ElIn tm | ElOut tm ->
      pp env fmt tm

    | CodePi (base, fam) when debug_mode ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "<∏>"
        (pp_atomic env) base
        (pp_atomic env) fam
    | CodePi (base, Lam (ident, fam)) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp env) base
        Uuseg_string.pp_utf_8 "→"
        (pp envx) fam
    | CodePi (base, tm) ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "∏"
        (pp_atomic env) base
        (pp_atomic env) tm

    | CodeSg (base, fam) when debug_mode ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "<Σ>"
        (pp_atomic env) base
        (pp_atomic env) fam
    | CodeSg (base, Lam (ident, fam)) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp env) base
        Uuseg_string.pp_utf_8 "×"
        (pp envx) fam
    | CodeSg (base, tm) ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "Σ"
        (pp_atomic env) base
        (pp_atomic env) tm
    | CodeRecord fields ->
       Format.fprintf fmt "@[record %a@]" (pp_fields env pp) fields
    | CodeExt (_, fam, `Global phi, bdry) ->
      Format.fprintf fmt "@[ext %a %a %a@]"
        (pp_atomic env) fam
        (pp_atomic Pp.Env.emp) phi
        (pp_atomic env) bdry

    | CodeNat when debug_mode ->
      Format.fprintf fmt "`nat"
    | CodeCircle when debug_mode ->
      Format.fprintf fmt "`circle"
    | CodeUniv when debug_mode ->
      Format.fprintf fmt "`type"
    | CodeNat ->
      Format.fprintf fmt "nat"
    | CodeCircle ->
      Format.fprintf fmt "circle"
    | CodeUniv ->
      Format.fprintf fmt "type"

    | Dim0 ->
      Format.fprintf fmt "0"
    | Dim1 ->
      Format.fprintf fmt "1"
    | Prf ->
      Format.fprintf fmt "*"
    | Ann (tm, _) ->
      pp env fmt tm
    | Let (tm, ident, bdy) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "@[let %a = %a in@ %a@]"
        Uuseg_string.pp_utf_8 x
        (pp env) tm
        (pp envx) bdy
    | Box (r, s, phi, sides, cap) when debug_mode ->
      Format.fprintf fmt "@[<hv2>box %a %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) phi
        (pp_atomic env) sides
        (pp_atomic env) cap
    | Box (_r, _s, _phi, sides, cap) ->
      pp_tuple (pp env) fmt [sides; cap]
    | Cap (r, s, phi, code, box) when debug_mode->
      Format.fprintf fmt "@[<hv2>cap %a %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) phi
        (pp_atomic env) code
        (pp_atomic env) box
    | Cap (_r, _s, _phi, _code, box) ->
      Format.fprintf fmt "@[<hv2>cap %a@]" (pp_atomic env) box
    | CodeV (r, pcode, code, pequiv) ->
      Format.fprintf fmt "@[<hv2>V %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) pcode
        (pp_atomic env) code
        (pp_atomic env) pequiv
    | VIn (r, equiv, pivot, base) when debug_mode ->
      Format.fprintf fmt "@[<hv2>vin %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) equiv
        (pp_atomic env) pivot
        (pp_atomic env) base
    | VIn (_, _, pivot, base) ->
      pp_tuple (pp env) fmt [pivot; base]
    | VProj (r, pcode, code, pequiv, v) when debug_mode ->
      Format.fprintf fmt "@[<hv2>vproj %a %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) pcode
        (pp_atomic env) code
        (pp_atomic env) pequiv
        (pp_atomic env) v
    | VProj (_, _, _, _, v) ->
      Format.fprintf fmt "@[<hv2>vproj %a@]"
        (pp_atomic env) v

    | ESub (sub, tm) ->
      Format.fprintf fmt "[%a]%a"
        (pp_sub env) sub
        (pp_atomic env) tm

    | LockedPrfIn prf ->
      Format.fprintf fmt "@[<hv2>lock %a@]"
        (pp_atomic env) prf

    | LockedPrfUnlock {cof; prf; bdy; _} ->
      Format.fprintf fmt "@[unlock %a : %a in@ %a@]"
        (pp env) prf
        (pp env) cof
        (pp env) bdy

  and pp_sub env fmt =
    function
    | Sb1 ->
      Uuseg_string.pp_utf_8 fmt "ε"
    | SbP ->
      Format.fprintf fmt "p"
    | SbI ->
      Format.fprintf fmt "id"
    | SbE (sb, tm) ->
      Format.fprintf fmt "%a, %a"
        (pp_atomic_sub env) sb
        (pp env) tm
    | SbC (sb0, sb1) ->
      Format.fprintf fmt "%a %a %a"
        (pp_atomic_sub env) sb0
        Uuseg_string.pp_utf_8 "∘"
        (pp_atomic_sub env) sb1

  and pp_atomic_sub env fmt sb =
    match sb with
    | Sb1 | SbP | SbI ->
      pp_sub env fmt sb
    | _ ->
      pp_braced (pp_sub env) fmt sb


  and pp_tp env fmt (tp : tp) =
    match tp with
    | TpCofSplit branches ->
      let sep fmt () = Format.fprintf fmt "@ | " in
      pp_list_group ~left:pp_lsq ~right:pp_rsq ~sep
        (pp_tp_cof_split_branch env)
        fmt
        branches
    | Pi (base, ident, fam) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env) base
        Uuseg_string.pp_utf_8 "→"
        (pp_tp envx) fam
    | Sg (base, ident, fam) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env) base
        Uuseg_string.pp_utf_8 "×"
        (pp_tp envx) fam
    | Record fields ->
       Format.fprintf fmt "record %a" (pp_fields env pp_tp) fields
    | Sub (tp, phi, tm) ->
      let _x, envx = ppenv_bind env `Anon in
      Format.fprintf fmt "@[sub %a %a@ %a@]"
        (pp_atomic_tp env) tp
        (pp_atomic env) phi
        (pp_atomic envx) tm
    | TpDim ->
      Format.fprintf fmt "𝕀"
    | TpCof ->
      Format.fprintf fmt "𝔽"
    | Univ ->
      Format.fprintf fmt "type"
    | Nat ->
      Format.fprintf fmt "nat"
    | Circle ->
      Format.fprintf fmt "circle"
    | El tm when debug_mode ->
      Format.fprintf fmt "el %a" (pp_atomic env) tm
    | El tm ->
      Format.fprintf fmt "%a" (pp env) tm
    | TpVar ix ->
      Format.fprintf fmt "#var[%i]" ix
    | TpPrf cof ->
      Format.fprintf fmt "[%a]" (pp env) cof
    | TpESub (sub, tp) ->
      Format.fprintf fmt "[%a]%a"
        (pp_sub env) sub
        (pp_atomic_tp env) tp
    | TpLockedPrf phi ->
      Format.fprintf fmt "locked %a"
        (pp_atomic env) phi

  and pp_atomic_tp env fmt tp =
    match tp with
    | TpDim | TpCof | Nat | Univ ->
      pp_tp env fmt tp
    | _ ->
      pp_braced (pp_tp env) fmt tp

  and pp_cof_split_branch env fmt (phi, tm) =
    let _x, envx = ppenv_bind env `Anon in
    Format.fprintf fmt "@[<hv>%a =>@ %a@]" (pp env) phi (pp envx) tm

  and pp_tp_cof_split_branch env fmt (phi, tm) =
    let _x, envx = ppenv_bind env `Anon in
    Format.fprintf fmt "@[<hv>%a =>@ %a@]" (pp env) phi (pp_tp envx) tm

  and pp_atomic env fmt tm =
    match tm with
    | Var _ | Global _ | Pair _ | CofSplit _ | Dim0 | Dim1 | Cof (Cof.Meet [] | Cof.Join []) | CodeNat | CodeCircle | CodeUniv
    | Zero | Base | Prf ->
      pp env fmt tm
    | Suc _ as tm when Option.is_some (to_numeral tm) ->
      pp env fmt tm
    | (SubIn tm | SubOut tm | ElIn tm | ElOut tm) when not debug_mode ->
      pp_atomic env fmt tm
    | _ ->
      pp_braced (pp env) fmt tm

  and pp_applications env fmt tm =
    match tm with
    | Ap (tm0, tm1) ->
      Format.fprintf fmt "%a %a" (pp_applications env) tm0 (pp_atomic env) tm1
    | (SubIn tm | SubOut tm | ElIn tm | ElOut tm) when not debug_mode ->
      pp_applications env fmt tm
    | _ ->
      pp env fmt tm

  and pp_lambdas env fmt tm =
    match tm with
    | Lam (nm, tm) ->
      let x, envx = ppenv_bind env nm in
      Format.fprintf fmt "%a %a"
        Uuseg_string.pp_utf_8 x
        (pp_lambdas envx) tm
    | (SubIn tm | SubOut tm | ElIn tm | ElOut tm) when not debug_mode ->
      pp_lambdas env fmt tm
    | _ ->
      Format.fprintf fmt "=>@ @[%a@]"
        (pp env) tm



  let pp_sequent_goal ~lbl env fmt tp  =
    let lbl = Option.value ~default:"" lbl in
    match tp with
    | Sub (tp, Cof (Cof.Join []), _) ->
      Format.fprintf fmt "?%a : @[<hov>%a@]"
        Uuseg_string.pp_utf_8 lbl
        (pp_tp env) tp
    | Sub (tp, phi, tm) ->
      let _x, envx = Pp.Env.bind env (Some "_") in
      Format.fprintf fmt "@[?%a : @[<hv>%a@ [%a => %a]@]"
        Uuseg_string.pp_utf_8 lbl
        (pp_tp env) tp
        (pp env) phi
        (pp envx) tm
    | tp ->
      Format.fprintf fmt "?%a : @[<hov>%a@]"
        Uuseg_string.pp_utf_8 lbl
        (pp_tp env) tp

  let rec pp_sequent_inner ~lbl env ctx fmt tp =
    match ctx with
    | [] ->
      Format.fprintf fmt "|- @[<hov>%a@]"
        (pp_sequent_goal ~lbl env)
        tp
    | (var, var_tp) :: ctx ->
      let x, envx = ppenv_bind env var in
      Fmt.fprintf fmt "%a : %a@;%a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env) var_tp
        (pp_sequent_inner ~lbl envx ctx) tp

  let pp_sequent ~lbl ctx : tp Pp.printer =
    fun fmt tp ->
    Format.fprintf fmt "@[<v>%a@]"
      (pp_sequent_inner ~lbl Pp.Env.emp ctx) tp
end
