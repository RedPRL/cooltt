open Basis
open Cubical

module Make (Symbol : Symbol.S) =
struct
  include SyntaxData.Make (Symbol)

  let to_numeral =
    let rec go acc =
      function
      | Zero -> Some acc
      | Suc t -> (go[@tailcall]) (acc+1) t
      | _ -> None
    in
    go 0

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

    | TeleNil -> Format.fprintf fmt "tele/nil"
    | TeleCons (x, code, tele) -> Format.fprintf fmt "tele/cons[%a, %a, %a]" Ident.pp_user x dump code dump tele
    | TeleElim (mot, nil, cons, tele) -> Format.fprintf fmt "tele/elim[%a, %a, %a, %a]" dump mot dump cons dump nil dump tele

    | Struct tele -> Format.fprintf fmt "struct[%a]" dump_struct tele
    | Proj (tm, lbl) -> Format.fprintf fmt "proj[%a, %a]" dump tm Ident.pp_user lbl

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
    | CodeTelescope -> Format.fprintf fmt "<tele>"
    | CodeSignature tele ->
      Format.fprintf fmt "sig[%a]"
        dump tele
    | CodeNat -> Format.fprintf fmt "nat"
    | CodeUniv -> Format.fprintf fmt "univ"
    | CodeV _ -> Format.fprintf fmt "<v>"
    | CodeCircle -> Format.fprintf fmt "circle"

    | ESub _ -> Format.fprintf fmt "<esub>"

    | LockedPrfIn _ -> Format.fprintf fmt "<locked/in>"
    | LockedPrfUnlock _ -> Format.fprintf fmt "<locked/unlock>"

  and dump_struct fmt tele =
    Format.fprintf fmt "%a" (Pp.pp_sep_list (fun fmt (lbl, tp) -> Format.fprintf fmt "%a : %a" Ident.pp_user lbl dump tp)) tele

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
    | Telescope -> Format.fprintf fmt "tp/tele"
    | Signature tele -> Format.fprintf fmt "tp/sig[%a]" dump tele
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

  module P =
  struct
    type tm = t (* anti-shadowing *)
    include SyntaxPrecedence

    let passed = nonassoc 12
    let atom = nonassoc 11
    let delimited = nonassoc 11
    let tuple = delimited
    let substitution = right 10
    let juxtaposition = left 9
    let cons = right 8
    let proj = right 8
    let sub_compose = left 7
    let cof_eq = nonassoc 6
    let cof_meet = nonassoc 5
    let cof_join = nonassoc 5
    let sub_comma = left 4
    let arrow = right 3
    let times = right 3
    let colon = nonassoc 2
    let double_arrow = right 1
    let in_ = nonassoc 0

    (** assumes [Debug.is_debug_mode ()] = [false] *)
    let classify_tm : tm -> t =
      function
      | Var _ | Global _ -> atom
      | Lam _ -> double_arrow
      | Ap _ -> juxtaposition
      | Pair _ -> tuple

      | TeleNil -> atom
      | TeleCons _ -> cons
      | TeleElim _ -> juxtaposition

      | Struct _ -> juxtaposition
      | Proj _ -> proj

      | CofSplit _ -> tuple
      | Cof (Cof.Eq _) -> cof_eq
      | Cof (Cof.Join [] | Cof.Meet []) -> atom
      | Cof (Cof.Join _) -> cof_join
      | Cof (Cof.Meet _) -> cof_meet
      | ForallCof _ -> dual juxtaposition arrow

      | Zero | Base | CodeNat | CodeCircle | CodeUniv | Dim0 | Dim1 | Prf -> atom
      | Suc _ as tm -> if Option.is_some (to_numeral tm) then atom else juxtaposition
      | HCom _ | Com _ | Coe _
      | Fst _ | Snd _
      | NatElim _ | Loop _
      | CircleElim _ -> juxtaposition

      | SubIn _ | SubOut _ | ElIn _ | ElOut _ -> passed
      | CodePi _ -> arrow
      | CodeSg _ -> times
      | CodeTelescope -> atom
      | CodeSignature _ -> juxtaposition
      | CodeExt _ -> juxtaposition

      | Ann _ -> passed
      | Let _ -> dual juxtaposition in_

      | Box _ -> tuple
      | Cap _ -> juxtaposition
      | CodeV _ -> juxtaposition
      | VIn _ -> tuple
      | VProj _ -> juxtaposition
      | ESub _ -> juxtaposition
      | LockedPrfIn _ -> juxtaposition
      | LockedPrfUnlock _ -> delimited

    let classify_sub : sub -> t =
      function
      | SbI | Sb1 | SbP -> atom
      | SbC _ -> sub_compose
      | SbE _ -> sub_comma

    let classify_tp : tp -> t =
      function
      | Univ | TpDim | TpCof | Nat | Circle -> atom
      | El _ -> passed
      | TpVar _ -> atom
      | TpPrf _ -> delimited
      | TpCofSplit _ -> delimited
      | Sub _ -> juxtaposition
      | Pi _ -> arrow
      | Sg _ -> times
      | Telescope -> atom
      | Signature _ -> juxtaposition
      | TpESub _ -> substitution
      | TpLockedPrf _ -> juxtaposition
  end

  let pp_var env fmt ix =
    Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var ix env

  let pp_bracketed pp fmt a =
    Format.fprintf fmt "@[<hv>[ %a@ ]@]"
      pp a

  let pp_bracketed_list ~pp_sep pp fmt xs =
    pp_bracketed (Format.pp_print_list ~pp_sep pp) fmt xs

  let pp_tuple pp =
    let pp_sep fmt () = Format.fprintf fmt "@ , " in
    pp_bracketed_list ~pp_sep pp

  let pp_braced pp fmt a =
    Format.fprintf fmt "{%a}"
      pp a

  let pp_braced_cond classify plain_pp penv fmt tm =
    if P.parens penv @@ classify tm then
      pp_braced (plain_pp penv) fmt tm
    else
      plain_pp penv fmt tm

  let ppenv_bind env ident =
    Pp.Env.bind env @@ Ident.to_string_opt ident

  let rec pp_tele pp_field env fmt  =
    function
    | [] -> ()
    | ((lbl, tp) :: tele) ->
      Format.fprintf fmt "(%a : %a)@ @,%a"
        Ident.pp_user lbl
        (pp_field env P.(right_of colon)) tp
        (pp_tele pp_field env) tele

  let rec pp env =
    pp_braced_cond P.classify_tm @@ fun penv fmt ->
    function
    | Lam _ as tm ->
      Format.fprintf fmt "@[%a@]"
        (pp_lambdas env) tm
    | Ap (tm0, tm1) ->
      Format.fprintf fmt "%a %a"
        (pp env P.(left_of juxtaposition)) tm0 (pp_atomic env) tm1
    | Pair (tm0, tm1) ->
      pp_tuple (pp env P.isolated) fmt [tm0; tm1]
    | TeleNil ->
      ()
    | TeleCons (ident, code, Lam (_, body)) ->
      let (x, envx) = ppenv_bind env (ident :> Ident.t) in
      Format.fprintf fmt "(%s : %a)@ @,%a"
        x
        (pp env P.(right_of colon)) code
        (pp envx penv) body
    | TeleCons (x, code, tele) ->
      Format.fprintf fmt "(%a : %a)@ @,%a"
        Ident.pp_user x
        (pp env P.(right_of colon)) code
        (pp env penv) tele
    | TeleElim (mot, nil, cons, tele) ->
      Format.fprintf fmt "@[<hv2>elim %a %@ %a@ @[<v>[ nil => %a@ | cons => %a@ ]@]@]"
        (pp_atomic env) tele
        (pp_atomic env) mot
        (pp env P.isolated) nil
        (pp env P.isolated) cons
    | Struct tele ->
      Format.fprintf fmt "@[struct %a@]" (pp_tele pp env) tele
    | Proj (tm, lbl) ->
      Format.fprintf fmt "@[%a %@ %a@]" (pp env P.(left_of proj)) tm Ident.pp_user lbl
    | CofSplit branches ->
      let pp_sep fmt () = Format.fprintf fmt "@ | " in
      pp_bracketed_list ~pp_sep (pp_cof_split_branch env) fmt branches
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
      Format.fprintf fmt "%a = %a" (pp env P.(left_of cof_eq)) r (pp env P.(right_of cof_eq)) s
    | Cof (Cof.Join []) ->
      Format.fprintf fmt "%a"
        Uuseg_string.pp_utf_8 "⊥"
    | Cof (Cof.Join phis) ->
      let pp_sep fmt () = Uuseg_string.pp_utf_8 fmt " ∨ " in
      Format.pp_print_list ~pp_sep (pp env P.(surrounded_by cof_join)) fmt phis
    | Cof (Cof.Meet []) ->
      Format.fprintf fmt "%a"
        Uuseg_string.pp_utf_8 "⊤"
    | Cof (Cof.Meet phis) ->
      let pp_sep fmt () = Uuseg_string.pp_utf_8 fmt " ∧ " in
      Format.pp_print_list ~pp_sep (pp env P.(surrounded_by cof_meet)) fmt phis
    | ForallCof phi ->
      let x, envx = ppenv_bind env `Anon in
      Format.fprintf fmt "%a %a %a %a"
        Uuseg_string.pp_utf_8 "∀"
        Uuseg_string.pp_utf_8 x
        Uuseg_string.pp_utf_8 "→"
        (pp envx P.(right_of arrow)) phi
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
      Format.fprintf fmt "@[<hv2>elim %a %@ %a@ @[<v>[ zero => %a@ | suc => %a@ ]@]@]"
        (pp_atomic env) tm
        (pp_atomic env) mot
        (pp env P.isolated) zero
        (pp env P.isolated) suc
    | Base ->
      Format.fprintf fmt "base"
    | Loop tm ->
      Format.fprintf fmt "loop %a" (pp_atomic env) tm
    | CircleElim (mot, base, loop, tm) ->
      Format.fprintf fmt "@[<hv2>elim %a %@ %a@ @[<v>[ base => %a@ | loop => %a@ ]@]@]"
        (pp_atomic env) tm
        (pp_atomic env) mot
        (pp env P.isolated) base
        (pp env P.isolated) loop
    | SubIn tm when Debug.is_debug_mode () ->
      Format.fprintf fmt "sub/in %a" (pp_atomic env) tm
    | SubOut tm when Debug.is_debug_mode () ->
      Format.fprintf fmt "sub/out %a" (pp_atomic env) tm
    | ElIn tm when Debug.is_debug_mode () ->
      Format.fprintf fmt "el/in %a" (pp_atomic env) tm
    | ElOut tm when Debug.is_debug_mode () ->
      Format.fprintf fmt "el/out %a" (pp_atomic env) tm
    | SubIn tm | SubOut tm | ElIn tm | ElOut tm ->
      pp env penv fmt tm

    | CodePi (base, fam) when Debug.is_debug_mode () ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "<∏>"
        (pp_atomic env) base
        (pp_atomic env) fam
    | CodePi (base, Lam (ident, fam)) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp env P.(right_of colon)) base
        Uuseg_string.pp_utf_8 "→"
        (pp envx P.(right_of arrow)) fam
    | CodePi (base, tm) ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "∏"
        (pp_atomic env) base
        (pp_atomic env) tm

    | CodeSg (base, fam) when Debug.is_debug_mode () ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "<Σ>"
        (pp_atomic env) base
        (pp_atomic env) fam
    | CodeSg (base, Lam (ident, fam)) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp env P.(right_of colon)) base
        Uuseg_string.pp_utf_8 "×"
        (pp envx P.(right_of times)) fam
    | CodeSg (base, tm) ->
      Format.fprintf fmt "@[%a %a %a@]"
        Uuseg_string.pp_utf_8 "Σ"
        (pp_atomic env) base
        (pp_atomic env) tm

    | CodeTelescope ->
      Format.fprintf fmt "tele"
    | CodeSignature tele ->
      Format.fprintf fmt "@[sig %a@]" (pp env penv) tele

    | CodeExt (_, fam, `Global phi, bdry) ->
      Format.fprintf fmt "@[ext %a %a %a@]"
        (pp_atomic env) fam
        (pp_atomic Pp.Env.emp) phi
        (pp_atomic env) bdry

    | CodeNat when Debug.is_debug_mode () ->
      Format.fprintf fmt "`nat"
    | CodeCircle when Debug.is_debug_mode () ->
      Format.fprintf fmt "`circle"
    | CodeUniv when Debug.is_debug_mode () ->
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
      pp env penv fmt tm
    | Let (tm, ident, bdy) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "@[let %a = %a in@ %a@]"
        Uuseg_string.pp_utf_8 x
        (pp env P.isolated) tm
        (pp envx P.(right_of in_)) bdy
    | Box (r, s, phi, sides, cap) when Debug.is_debug_mode () ->
      Format.fprintf fmt "@[<hv2>box %a %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) s
        (pp_atomic env) phi
        (pp_atomic env) sides
        (pp_atomic env) cap
    | Box (_r, _s, _phi, sides, cap) ->
      pp_tuple (pp env P.isolated) fmt [sides; cap]
    | Cap (r, s, phi, code, box) when Debug.is_debug_mode ()->
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
    | VIn (r, equiv, pivot, base) when Debug.is_debug_mode () ->
      Format.fprintf fmt "@[<hv2>vin %a %a %a %a@]"
        (pp_atomic env) r
        (pp_atomic env) equiv
        (pp_atomic env) pivot
        (pp_atomic env) base
    | VIn (_, _, pivot, base) ->
      pp_tuple (pp env P.isolated) fmt [pivot; base]
    | VProj (r, pcode, code, pequiv, v) when Debug.is_debug_mode () ->
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
        (pp_sub env P.isolated) sub
        (pp env P.(right_of substitution)) tm

    | LockedPrfIn prf ->
      Format.fprintf fmt "@[<hv2>lock %a@]"
        (pp_atomic env) prf

    | LockedPrfUnlock {cof; prf; bdy; _} ->
      Format.fprintf fmt "@[unlock %a : %a in@ %a@]"
        (pp env P.(left_of colon)) prf
        (pp env P.(right_of colon)) cof
        (pp env P.(right_of in_)) bdy

  and pp_sub env =
    pp_braced_cond P.classify_sub @@ fun _ fmt ->
    function
    | Sb1 ->
      Uuseg_string.pp_utf_8 fmt "ε"
    | SbP ->
      Format.fprintf fmt "p"
    | SbI ->
      Format.fprintf fmt "id"
    | SbE (sb, tm) ->
      Format.fprintf fmt "%a, %a"
        (pp_sub env P.(left_of sub_comma)) sb
        (pp env P.(right_of sub_comma)) tm
    | SbC (sb0, sb1) ->
      Format.fprintf fmt "%a %a %a"
        (pp_sub env P.(left_of sub_compose)) sb0
        Uuseg_string.pp_utf_8 "∘"
        (pp_sub env P.(right_of sub_compose)) sb1

  and pp_tp env =
    pp_braced_cond P.classify_tp @@ fun penv fmt ->
    function
    | TpCofSplit branches ->
      let pp_sep fmt () = Format.fprintf fmt "@ | " in
      pp_bracketed_list ~pp_sep
        (pp_tp_cof_split_branch env)
        fmt
        branches
    | Pi (base, ident, fam) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env P.(right_of colon)) base
        Uuseg_string.pp_utf_8 "→"
        (pp_tp envx P.(right_of arrow)) fam
    | Sg (base, ident, fam) ->
      let x, envx = ppenv_bind env ident in
      Format.fprintf fmt "(%a : %a) %a %a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env P.(right_of colon)) base
        Uuseg_string.pp_utf_8 "×"
        (pp_tp envx P.(right_of times)) fam
    | Telescope ->
      Format.fprintf fmt "tele"
    | Signature tele ->
      Format.fprintf fmt "sig %a" (pp env penv) tele
    | Sub (tp, phi, tm) ->
      let _x, envx = ppenv_bind env `Anon in
      Format.fprintf fmt "@[sub %a %a@ %a@]"
        (pp_tp env P.(right_of juxtaposition)) tp
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
    | El tm when Debug.is_debug_mode () ->
      Format.fprintf fmt "el %a" (pp_atomic env) tm
    | El tm ->
      pp env penv fmt tm
    | TpVar ix ->
      Format.fprintf fmt "#var[%i]" ix
    | TpPrf cof ->
      pp_bracketed (pp env P.isolated) fmt cof
    | TpESub (sub, tp) ->
      Format.fprintf fmt "[%a]%a"
        (pp_sub env P.isolated) sub
        (pp_tp env P.(right_of substitution)) tp
    | TpLockedPrf phi ->
      Format.fprintf fmt "locked %a"
        (pp_atomic env) phi

  and pp_cof_split_branch env fmt (phi, tm) =
    let _x, envx = ppenv_bind env `Anon in
    Format.fprintf fmt "@[<hv>%a =>@ %a@]"
      (pp env P.(left_of double_arrow)) phi
      (pp envx P.(right_of double_arrow)) tm

  and pp_tp_cof_split_branch env fmt (phi, tm) =
    let _x, envx = ppenv_bind env `Anon in
    Format.fprintf fmt "@[<hv>%a =>@ %a@]"
      (pp env P.(left_of double_arrow)) phi
      (pp_tp envx P.(right_of double_arrow)) tm

  (* XXX [pp_atomic] should have been removed, but it was kept to minimize git diff. It now means printing the term to the right of the juxtaposition operator, like [arg] in [f arg]. The fine-grained control brought by {!module:SyntaxPrecedence} obsoletes the old classification of terms. *)
  and pp_atomic env fmt tm =
    pp env P.(right_of juxtaposition) fmt tm

  and pp_lambdas env fmt tm =
    match tm with
    | Lam (nm, tm) ->
      let x, envx = ppenv_bind env nm in
      Format.fprintf fmt "%a %a"
        Uuseg_string.pp_utf_8 x
        (pp_lambdas envx) tm
    | (SubIn tm | SubOut tm | ElIn tm | ElOut tm) when not @@ Debug.is_debug_mode () ->
      pp_lambdas env fmt tm
    | _ ->
      Format.fprintf fmt "=>@ @[%a@]"
        (pp env P.(right_of double_arrow)) tm

  (* Pretty print a term that uses lambdas as binders. *)
  and pp_binders env penv fmt tm =
    match tm with
    | Lam (nm, tm) ->
      let x, envx = ppenv_bind env nm in
      if Debug.is_debug_mode ()
      then Format.fprintf fmt "`{%s} =>@ @[%a@]" x (pp_binders envx penv) tm
      else pp_binders envx penv fmt tm
    | _ -> pp env penv fmt tm

  let pp_sequent_boundary env fmt tm =
    let rec pp_branches env fmt (bdry, cons) =
      match cons with
      | CofSplit branches ->
        let _x, envx = ppenv_bind env `Anon in
        Format.pp_print_list ~pp_sep:(Format.pp_print_cut) (pp_branches envx) fmt branches
      | _ -> pp_cof_split_branch env fmt (bdry, cons)
    in
    match tm with
    | CofSplit branches when not (CCList.is_empty branches) ->
      Format.pp_print_list ~pp_sep:(Format.pp_print_cut) (pp_branches env) fmt branches
    | _ -> pp env P.isolated fmt tm

  let rec pp_in_ctx env ctx pp_goal fmt goal =
    match ctx with
    | [] -> pp_goal env fmt goal
    | (var, var_tp) :: ctx ->
      let x, envx = ppenv_bind env var in
      Fmt.fprintf fmt "%a : %a@;%a"
        Uuseg_string.pp_utf_8 x
        (pp_tp env P.(right_of colon)) var_tp
        (pp_in_ctx envx ctx pp_goal) goal

  let rec get_constraints =
    function
    | Sub (tp, Cof (Cof.Join []), _) -> get_constraints tp
    | Sub (tp, phi, tm) -> `Boundary (tp, phi, tm)
    | El (CodeExt (0, tp, `Global phi, (Lam (_, tm)))) -> `Boundary (El tp, phi, tm)
    | tp -> `Unconstrained tp

  let pp_sequent_goal ~lbl env fmt tp  =
    let lbl = Option.value ~default:"" lbl in
    match get_constraints tp with
    | `Boundary (tp, phi, tm) ->
      let _x, envx = Pp.Env.bind env (Some "_") in
      Format.fprintf fmt "|- ?%a : @[<hov>%a@]@,@,Boundary:@,%a@,|- @[<v>%a@]"
        Uuseg_string.pp_utf_8 lbl
        (pp_tp env P.(right_of colon)) tp
        (pp env P.(right_of colon))
        phi
        (pp_sequent_boundary envx)
        tm
    | `Unconstrained tp ->
      Format.fprintf fmt "|- ?%a : @[<hov>%a@]"
        Uuseg_string.pp_utf_8 lbl
        (pp_tp env P.(right_of colon)) tp

  let pp_sequent ~lbl ctx : tp Pp.printer =
    fun fmt tp ->
    Format.fprintf fmt "@[<v>%a@]"
      (pp_in_ctx Pp.Env.emp ctx (pp_sequent_goal ~lbl)) tp

  let pp_boundary_sat fmt =
    function
    | `BdrySat -> Format.pp_print_string fmt "satisfied"
    | `BdryUnsat -> Format.pp_print_string fmt "unsatisfied"

  let pp_partial_sequent_goal bdry_sat env fmt (partial, tp) =
    match get_constraints tp with
    | `Boundary (tp, phi, tm) ->
      let _x, envx = Pp.Env.bind env (Some "_") in
      Format.fprintf fmt "|- {! %a !} : @[<hov>%a@]@,@,Boundary (%a):@,%a@,|- @[<v>%a@]"
        (pp env P.(right_of colon)) partial
        (pp_tp env P.(right_of colon)) tp
        pp_boundary_sat bdry_sat
        (pp env P.(right_of colon)) phi
        (pp_sequent_boundary envx) tm
    | `Unconstrained tp ->
      Format.fprintf fmt "|- {! %a !} : @[<hov>%a@]"
        (pp env P.(right_of colon)) partial
        (pp_tp env P.(right_of colon)) tp

  let pp_partial_sequent bdry_sat ctx : (t * tp) Pp.printer =
    fun fmt goal ->
    Format.fprintf fmt "@[<v>%a@]"
      (pp_in_ctx Pp.Env.emp ctx (pp_partial_sequent_goal bdry_sat)) goal

  let pp env = pp env P.isolated
  let pp_tp env = pp_tp env P.isolated
end
