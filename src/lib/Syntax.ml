open CoolBasis open Bwd
include SyntaxData

let rec condense = 
  function
  | Zero -> Some 0
  | Suc t -> 
    begin
      match condense t with
      | Some n -> Some (n + 1)
      | None -> None
    end
  | _ -> None


module Fmt = Format

let pp_var env fmt ix = 
  Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var ix env

let rec pp_ (env : Pp.env) (mode : [`Start | `Lam | `Ap]) fmt tm =
  match mode, tm with
  | `Lam, Lam ((Lam _) as tm) ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "%a %a" 
      Uuseg_string.pp_utf_8 x 
      (pp_ envx `Lam) tm
  | `Lam, Lam tm ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "%a%a" 
      Uuseg_string.pp_utf_8 x 
      (pp_ envx `Lam) tm
  | `Lam, tm ->
    Fmt.fprintf fmt "%s@ %a" "]" (pp env) tm
  | _, (Lam _ as tm) ->
    Fmt.fprintf fmt "@[<hov1>(lam %s%a)@]" "[" (pp_ env `Lam) (Lam tm)
  | _, Var i -> 
    pp_var env fmt i
  | _, Global sym ->
    Symbol.pp fmt sym
  | _, Let (tm, bnd) ->
    let x, env' = Pp.Env.bind env None in
    Fmt.fprintf fmt 
      "@[<hov1>(let@ @[<hov1>[%a %a]@]@ %a)@]" 
      Uuseg_string.pp_utf_8 x 
      (pp env) tm 
      (pp env') bnd
  | _, Ann (tm, tp) ->
    Fmt.fprintf fmt "@[<hov1>(: @[<hov>%a@ %a@])@]" 
      (pp_tp env) tp
      (pp env) tm
  | _, Coe (code, r, s, tm) ->
    Fmt.fprintf fmt "@[<hov1>(coe@ %a@ %a@ %a@ %a)@]"
      (pp env) code
      (pp env) r 
      (pp env) s
      (pp env) tm
  | _, HCom (code, r, s, phi, tm) ->
    Fmt.fprintf fmt "@[<hov1>(hcom@ %a@ %a %a@ %a@ %a)@]"
      (pp env) code
      (pp env) r 
      (pp env) s
      (pp env) phi
      (pp env) tm
  | _, Com (code, r, s, phi, tm) ->
    Fmt.fprintf fmt "@[<hov1>(com@ %a@ %a %a@ %a@ %a)@]"
      (pp env) code
      (pp env) r 
      (pp env) s
      (pp env) phi
      (pp env) tm
  | _, Zero ->
    Fmt.fprintf fmt "0"
  | _, Suc tm ->
    begin
      match condense tm with 
      | Some n -> Fmt.fprintf fmt "%d" @@ n + 1
      | None -> Fmt.fprintf fmt "@[<hov1>(suc@ %a)@]" (pp env) tm
    end
  | _, NatElim (Some ghost, _, _, _, scrut) ->
    pp_ghost_ env mode fmt (ghost, scrut)
  | _, IdElim (Some ghost, _, _, scrut) ->
    pp_ghost_ env mode fmt (ghost, scrut)
  | _, NatElim (None, mot, zero, suc, scrut) ->
    let x, envx = Pp.Env.bind env None in
    let y, envxy = Pp.Env.bind envx None in
    Fmt.fprintf fmt
      "@[<hov1>(nat.elim@ [%a] %a @[<hov1>(zero@ %a)@]@ @[<hov1>(suc@ [%a %a] %a)@]@ %a)@]"
      Uuseg_string.pp_utf_8 x 
      (pp_tp envx) mot
      (pp env) zero
      Uuseg_string.pp_utf_8 x 
      Uuseg_string.pp_utf_8 y
      (pp envxy) suc
      (pp env) scrut
  | _, IdElim (_, mot, refl, scrut) ->
    let x, envx = Pp.Env.bind env None in
    let y, envxy = Pp.Env.bind envx None in
    let z, envxyz = Pp.Env.bind envxy None in
    Fmt.fprintf fmt
      "@[<hov1>(id.elim@ [%a %a %a] %a@ @[<hov1>(refl@ [%a] %a)@]@ %a@]"
      Uuseg_string.pp_utf_8 x
      Uuseg_string.pp_utf_8 y
      Uuseg_string.pp_utf_8 z
      (pp_tp envxyz) mot 
      Uuseg_string.pp_utf_8 x
      (pp envx) refl
      (pp env) scrut
  | _, Fst tm ->
    Fmt.fprintf fmt "@[<hov1>(fst@ %a)@]" (pp env) tm
  | _, Snd tm ->
    Fmt.fprintf fmt "@[<hov1>(snd@ %a)@]" (pp env) tm
  | `Ap, Ap (tm0, tm1) ->
    Fmt.fprintf fmt "%a@ %a" (pp_ env `Ap) tm0 (pp env) tm1
  | _, Ap (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hov1>(%a@ %a)@]" (pp_ env `Ap) tm0 (pp env) tm1
  | _, Pair (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hov1>(pair@ %a@ %a)@]" (pp env) tm0 (pp env) tm1
  | _, Refl tm ->
    Fmt.fprintf fmt "@[<hov1>(refl %a)@]" (pp env) tm
  | _, GoalRet tm ->
    Fmt.fprintf fmt "@[<hov1>(goal-ret %a)@]" (pp env) tm
  | _, GoalProj tm ->
    Fmt.fprintf fmt "@[<hov1>(goal-proj %a)@]" (pp env) tm
  | _, SubIn tm ->
    Fmt.fprintf fmt "@[<hov1>(sub/in@ %a)@]" (pp env) tm
  | _, SubOut tm ->
    Fmt.fprintf fmt "@[<hov1>(sub/out@ %a)@]" (pp env) tm
  | _, Dim0 ->
    Fmt.fprintf fmt "0"
  | _, Dim1 ->
    Fmt.fprintf fmt "1"
  | _, Cof Cof.Bot -> 
    Fmt.fprintf fmt "false"
  | _, Cof Cof.Top -> 
    Fmt.fprintf fmt "true"
  | _, Cof (Cof.Join (phi, psi)) -> 
    Fmt.fprintf fmt "@[<hov1>(or %a %a)@]"
      (pp env) phi
      (pp env) psi
  | _, Cof (Cof.Meet (phi, psi)) -> 
    Fmt.fprintf fmt "@[<hov1>(and %a %a)@]"
      (pp env) phi
      (pp env) psi
  | _, Cof (Cof.Eq (r, s)) ->
    Fmt.fprintf fmt "@[<hov1>(= %a %a)@]"
      (pp env) r 
      (pp env) s
  | _, CofAbort ->
    Fmt.fprintf fmt "[]"
  | _, CofSplit (_, phi0, phi1, tm0, tm1) ->
    let _, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hov1>(split@ [%a %a]@ [%a %a])@]"
      (pp env) phi0
      (pp envx) tm0
      (pp env) phi1
      (pp envx) tm1
  | _, Prf ->
    Fmt.fprintf fmt "*"
  | _, CodePath _ ->
    Fmt.fprintf fmt "<CodePath>"
  | _, CodePi _ ->
    Fmt.fprintf fmt "<CodePi>"
  | _, CodeSg _ ->
    Fmt.fprintf fmt "<CodeSg>"
  | _, CodeNat -> 
    Fmt.fprintf fmt "<CodeNat>"

and pp env = pp_ env `Start

and pp_ghost_ env mode fmt ((name, cells), scrut) =
  let rec go_cells env fmt =
    function 
    | [] -> pp env fmt scrut
    | (_, tm) :: cells -> 
      Fmt.fprintf fmt "%a@ %a" (pp env) tm (go_cells env) cells
  in
  match mode with
  | `Ap ->
    Fmt.fprintf fmt "%a@ %a" pp_problem name (go_cells env) cells
  | _ ->
    Fmt.fprintf fmt "@[<hov1>(%a@ %a)@]" pp_problem name (go_cells env) cells

and pp_ghost env =
  pp_ghost_ env `Start

and pp_problem fmt problem =
  let lbls = Bwd.to_list problem in
  let dot fmt () = Fmt.fprintf fmt "." in
  Fmt.pp_print_list ~pp_sep:dot Uuseg_string.pp_utf_8 fmt lbls


and pp_tp_ (env : Pp.env) (mode : _) : tp Pp.printer = 
  fun fmt tp ->
  match mode, tp with 
  | `Pi, Pi (base, fam) 
  | `Sg, Sg (base, fam)-> 
    let x, envx = Pp.Env.bind env None in
    Format.fprintf fmt "[%a : %a]@ %a"
      Uuseg_string.pp_utf_8 x
      (pp_tp env) base
      (pp_tp_ envx mode) fam
  | (`Pi | `Sg), _-> 
    Format.fprintf fmt "@]@ %a" 
      (pp_tp env) tp
  | _, Pi _ -> 
    Format.fprintf fmt "@[<hv1>(->@ @[%a)@]" (pp_tp_ env `Pi) tp
  | _, Sg _ -> 
    Format.fprintf fmt "@[<hv1>(*@ @[%a)@]" (pp_tp_ env `Sg) tp
  | _, Univ ->
    Format.fprintf fmt "univ"
  | _, El tm ->
    Fmt.fprintf fmt "@[<hov1>(el@ %a)@]" (pp env) tm
  | _, Sub (tp, phi, t) ->
    let x, envx = Pp.Env.bind env None in
    Format.fprintf fmt 
      "@[<hv1>(sub@ %a@ %a@ %a)@]"
      (pp_tp env) tp
      (pp env) phi
      (pp envx) t
  | _, GoalTp (None, tp) ->
    Fmt.fprintf fmt "@[<hov1>(goal@ _@ %a)@]" (pp_tp env) tp
  | _, GoalTp (Some lbl, tp) ->
    Fmt.fprintf fmt "@[<hov1>(goal@ ?%a@ %a)@]" 
      Uuseg_string.pp_utf_8 lbl 
      (pp_tp env) tp
  | _, TpDim ->
    Format.fprintf fmt "dim"
  | _, TpCof ->
    Format.fprintf fmt "cof"
  | _, TpPrf phi->
    Format.fprintf fmt "@[<hov1>(prf@ %a)@]"
      (pp env) phi
  | _, Id (tp, tm0, tm1) -> 
    Format.fprintf fmt "@[<hov1>(id@ @[<hv>%a@ %a@ %a@])@]"
      (pp_tp env) tp
      (pp env) tm0
      (pp env) tm1
  | _, Nat ->
    Format.fprintf fmt "nat"
  | _, TpVar i ->
    Format.fprintf fmt "(tpvar %i)" i

and pp_tp env = pp_tp_ env `Start

let pp_sequent_goal env fmt tp  =
  match tp with
  | GoalTp (olbl, Sub (tp, Cof Cof.Bot, _)) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    Format.fprintf fmt "?%a : @[<hov>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
  | GoalTp (olbl, Sub (tp, phi, tm)) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    let x, envx = Pp.Env.bind env None in
    Format.fprintf fmt "@[?%a : @[<hv>%a@ [%a : %a => %a]@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
      Uuseg_string.pp_utf_8 x 
      (pp env) phi
      (pp envx) tm
  | GoalTp (olbl, tp) ->
    let lbl = match olbl with Some lbl -> lbl | None -> "" in
    Format.fprintf fmt "?%a : @[<hov>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
  | tp ->
    pp_tp env fmt tp

let rec pp_sequent_inner ~names env fmt tp =
  match names, tp with
  | nm :: names, Pi (base, fam) ->
    let x, envx = Pp.Env.bind env @@ Some nm in
    Fmt.fprintf fmt "%a : %a@;%a"
      Uuseg_string.pp_utf_8 x
      (pp_tp env) base
      (pp_sequent_inner ~names envx) fam
  | _, tp ->
    Format.fprintf fmt "|- @[<hov>%a@]"
      (pp_sequent_goal env) 
      tp

let pp_sequent ~names : tp Pp.printer =
  fun fmt tp ->
  Format.fprintf fmt "@[<v>%a@]"
    (pp_sequent_inner ~names Pp.Env.emp) tp

type env = tp list

