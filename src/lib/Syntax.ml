open CoolBasis open Bwd
include SyntaxData

let debug_mode = false

let rec to_numeral =
  function
  | Zero -> Some 0
  | Suc t ->
    Option.map (fun n -> n + 1) @@
    to_numeral t
  | _ -> None


module Fmt = Format

let rec dump fmt tm =
  match tm with
  | CodePi _ -> Format.fprintf fmt "<pi>"
  | CodePath _ -> Format.fprintf fmt "<?>"
  | CodeSg _ -> Format.fprintf fmt "<?>"
  | Fst tm -> Format.fprintf fmt "fst[%a]" dump tm
  | Snd tm -> Format.fprintf fmt "snd[%a]" dump tm
  | Pair (tm0, tm1) -> Format.fprintf fmt "pair[%a, %a]" dump tm0 dump tm1
  | Var i -> Format.fprintf fmt "var[%i]" i
  | Lam _ -> Format.fprintf fmt "<lam>"
  | Ap (tm0, tm1) -> Format.fprintf fmt "ap[%a, %a]" dump tm0 dump tm1
  | GoalRet _ -> Format.fprintf fmt "<goal-ret>"
  | GoalProj _ -> Format.fprintf fmt "<goal-proj>"
  | Coe _ -> Format.fprintf fmt "<coe>"
  | HCom _ -> Format.fprintf fmt "<hcom>"
  | Com _ -> Format.fprintf fmt "<com>"
  | SubIn _ -> Format.fprintf fmt "<sub/in>"
  | SubOut _ -> Format.fprintf fmt "<sub/out>"
  | ElIn _ -> Format.fprintf fmt "<el/in>"
  | ElOut _ -> Format.fprintf fmt "<el/out>"
  | Cof _ -> Format.fprintf fmt "<cof>"
  | CofSplit _ -> Format.fprintf fmt "<cof/split>"
  | Zero -> Format.fprintf fmt "<zero>"
  | Suc _ -> Format.fprintf fmt "<suc>"
  | Dim0 -> Format.fprintf fmt "<dim0>"
  | Dim1 -> Format.fprintf fmt "<dim1>"
  | _ -> Format.fprintf fmt "<??>"

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
  Pp.Env.bind env @@
  match ident with
  | `Anon -> None
  | `User id -> Some id
  | `Machine id -> Some id

let rec pp env fmt tm =
  match tm with
  | Lam _ ->
    Format.fprintf fmt "@[%a@]"
      (pp_lambdas env) tm
  | Ap _ ->
    pp_applications env fmt tm
  | Pair (tm0, tm1) ->
    pp_tuple (pp env) fmt [tm0; tm1]
  | CofAbort ->
    Format.fprintf fmt "[]"
  | CofSplit (_, branches) ->
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
  | GoalRet tm when debug_mode ->
    Format.fprintf fmt "goal/in %a" (pp_atomic env) tm
  | GoalProj tm when debug_mode ->
    Format.fprintf fmt "goal/out %a" (pp_atomic env) tm
  | SubIn tm | SubOut tm | GoalRet tm | GoalProj tm | ElIn tm | ElOut tm ->
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

  | CodePath (fam, bdry) when debug_mode ->
    Format.fprintf fmt "@[`path %a %a@]"
      (pp_atomic env) fam
      (pp_atomic env) bdry

  | CodePath (fam, bdry) ->
    Format.fprintf fmt "@[ext {i => ∂ i} %a %a@]"
      (pp_atomic env) fam
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
  | Box (r, s, phi, sides, cap) ->
    Format.fprintf fmt "@[<hv2>box %a %a %a %a %a@]"
      (pp_atomic env) r
      (pp_atomic env) s
      (pp_atomic env) phi
      (pp_atomic env) sides
      (pp_atomic env) cap
  | Cap (r, s, phi, code, box) ->
    Format.fprintf fmt "@[<hv2>cap %a %a %a %a %a@]"
      (pp_atomic env) r
      (pp_atomic env) s
      (pp_atomic env) phi
      (pp_atomic env) code
      (pp_atomic env) box
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
  | VProj (r, equiv, v) when debug_mode ->
    Format.fprintf fmt "@[<hv2>vproj %a %a %a@]"
      (pp_atomic env) r
      (pp_atomic env) equiv
      (pp_atomic env) v
  | VProj (r, equiv, v) ->
    Format.fprintf fmt "@[<hv2>vproj %a@]"
      (pp_atomic env) v

and pp_tp env fmt tp =
  match tp with
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
  | Sub (tp, phi, tm) ->
    let x, envx = ppenv_bind env `Anon in
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
  | GoalTp (_, tp) ->
    pp_tp env fmt tp
  | TpPrf cof ->
    Format.fprintf fmt "[%a]" (pp env) cof

and pp_atomic_tp env fmt tp =
  match tp with
  | TpDim | TpCof | Nat | Univ ->
    pp_tp env fmt tp
  | _ ->
    pp_braced (pp_tp env) fmt tp

and pp_cof_split_branch env fmt (phi, tm) =
  let x, envx = ppenv_bind env `Anon in
  Format.fprintf fmt "@[<hv>%a =>@ %a@]" (pp env) phi (pp envx) tm

and pp_atomic env fmt tm =
  match tm with
  | Var _ | Global _ | Pair _ | CofAbort | CofSplit _ | Dim0 | Dim1 | Cof (Cof.Meet [] | Cof.Join []) | CodeNat | CodeCircle | CodeUniv
  | Zero | Base | Prf ->
    pp env fmt tm
  | (SubIn tm | SubOut tm | GoalRet tm | GoalProj tm | ElIn tm | ElOut tm) when not debug_mode ->
    pp_atomic env fmt tm
  | _ ->
    pp_braced (pp env) fmt tm

and pp_applications env fmt tm =
  match tm with
  | Ap (tm0, tm1) ->
    Format.fprintf fmt "%a %a" (pp_applications env) tm0 (pp_atomic env) tm1
  | (SubIn tm | SubOut tm | GoalRet tm | GoalProj tm | ElIn tm | ElOut tm) when not debug_mode ->
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
  | (SubIn tm | SubOut tm | GoalRet tm | GoalProj tm | ElIn tm | ElOut tm) when not debug_mode ->
    pp_lambdas env fmt tm
  | _ ->
    Format.fprintf fmt "=>@ @[%a@]"
      (pp env) tm



let pp_sequent_goal env fmt tp  =
  match tp with
  | GoalTp (olbl, Sub (tp, Cof (Cof.Join []), _)) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    Format.fprintf fmt "?%a : @[<hov>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
  | GoalTp (olbl, Sub (tp, phi, tm)) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    let x, envx = Pp.Env.bind env (Some "_") in
    Format.fprintf fmt "@[?%a : @[<hv>%a@ [%a => %a]@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
      (pp env) phi
      (pp envx) tm
  | GoalTp (olbl, tp) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    Format.fprintf fmt "?%a : @[<hov>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
  | tp ->
    pp_tp env fmt tp

let rec pp_sequent_inner env fmt tp =
  match tp with
  | Pi (base, ident, fam) ->
    let x, envx = ppenv_bind env ident in
    Fmt.fprintf fmt "%a : %a@;%a"
      Uuseg_string.pp_utf_8 x
      (pp_tp env) base
      (pp_sequent_inner envx) fam
  | tp ->
    Format.fprintf fmt "|- @[<hov>%a@]"
      (pp_sequent_goal env)
      tp

let pp_sequent : tp Pp.printer =
  fun fmt tp ->
  Format.fprintf fmt "@[<v>%a@]"
    (pp_sequent_inner Pp.Env.emp) tp

type env = tp list
