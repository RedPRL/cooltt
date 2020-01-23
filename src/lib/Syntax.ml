open CoolBasis open Bwd

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Global of Symbol.t
  | Let of t * (* BINDS *) t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of ghost option * (* BINDS *) tp * t * (* BINDS 2 *) t * t
  | Lam of (* BINDS *) t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of ghost option * (* BINDS 3 *) tp * (* BINDS *) t * t
  | CodeNat
  | CodePi of t * t
  | GoalRet of t
  | GoalProj of t
[@@deriving show]

and tp =
  | Nat
  | Pi of tp * (* BINDS *) tp
  | Sg of tp * (* BINDS *) tp
  | Id of tp * t * t
  | Univ
  | El of t
  | GoalTp of string option * tp
[@@deriving show]

and ghost = string bwd * (tp * t) list
[@@deriving show]

let rec condense = function
  | Zero -> Some 0
  | Suc t -> (
      match condense t with
      | Some n -> Some (n + 1)
      | None -> None )
  | _ -> None


module Fmt = Format

let rec pp_ (env : Pp.env)  =
  let rec go env (mode : [`Start | `Lam  | `Pi | `Ap]) fmt tm= 
    match mode, tm with
    | _, Var i -> 
      Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var i env
    | _, Global sym ->
      Symbol.pp fmt sym
    | _, Let (tm, bnd) ->
      let x, env' = Pp.Env.bind env None in
      Fmt.fprintf fmt 
        "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) tm 
        (go env' `Start) bnd
    | _, Ann (tm, tp) ->
      Fmt.fprintf fmt "@[<hv1>(: @[<hov>%a@ %a@])@]" 
        (pp_tp_ env) tp 
        (go env `Start) tm
    | _, Zero ->
      Fmt.fprintf fmt "0"
    | _, Suc tm ->
      begin
        match condense tm with 
        | Some n -> Fmt.fprintf fmt "%d" @@ n + 1
        | None -> Fmt.fprintf fmt "@[<hv1>(suc@ %a)@]" (go env `Start) tm
      end
    | _, NatElim (Some ghost, _, _, _, scrut) ->
      pp_ghost_ env fmt (ghost, scrut)
    | _, IdElim (Some ghost, _, _, scrut) ->
      pp_ghost_ env fmt (ghost, scrut)
    | _, NatElim (None, mot, zero, suc, scrut) ->
      let x, envx = Pp.Env.bind env None in
      let y, envxy = Pp.Env.bind envx None in
      Fmt.fprintf fmt
        "@[<hv1>(nat.elim@ [%a] %a @[<hv1>(zero@ %a)@]@ @[<hv1>(suc@ [%a %a] %a)@]@ %a)@]"
        Uuseg_string.pp_utf_8 x 
        (pp_tp_ envx) mot
        (go env `Start) zero
        Uuseg_string.pp_utf_8 x 
        Uuseg_string.pp_utf_8 y
        (go envxy `Start) suc
        (go env `Start) scrut
    | _, IdElim (_, mot, refl, scrut) ->
      let x, envx = Pp.Env.bind env None in
      let y, envxy = Pp.Env.bind envx None in
      let z, envxyz = Pp.Env.bind envxy None in
      Fmt.fprintf fmt
        "@[<hv1>(id.elim@ [%a %a %a] %a@ @[<hv1>(refl@ [%a] %a)@]@ %a@]"
        Uuseg_string.pp_utf_8 x
        Uuseg_string.pp_utf_8 y
        Uuseg_string.pp_utf_8 z
        (pp_tp_ envxyz) mot 
        Uuseg_string.pp_utf_8 x
        (go envx `Start) refl
        (go env `Start) scrut
    | `Lam, Lam tm ->
      let x, envx = Pp.Env.bind env None in
      Fmt.fprintf fmt "[%a] %a" 
        Uuseg_string.pp_utf_8 x 
        (go envx `Lam) tm
    | _, Lam tm ->
      let x, envx = Pp.Env.bind env None in
      Fmt.fprintf fmt "@[<hv1>(lam@ [%a] %a)@]" 
        Uuseg_string.pp_utf_8 x 
        (go envx `Lam) tm
    | _, Fst tm ->
      Fmt.fprintf fmt "@[<hv1>(fst@ %a)@]" (go env `Start) tm
    | _, Snd tm ->
      Fmt.fprintf fmt "@[<hv1>(snd@ %a)@]" (go env `Start) tm
    | `Ap, Ap (tm0, tm1) ->
      Fmt.fprintf fmt "%a@ %a" (go env `Ap) tm0 (go env `Start) tm1
    | _, Ap (tm0, tm1) ->
      Fmt.fprintf fmt "@[<hv1>(%a@ %a)@]" (go env `Ap) tm0 (go env `Start) tm1
    | _, Pair (tm0, tm1) ->
      Fmt.fprintf fmt "@[<hv1>(pair@ %a@ %a)@]" (go env `Start) tm0 (go env `Start) tm1
    | _, Refl tm ->
      Fmt.fprintf fmt "@[<hv1>(refl %a)@]" (go env `Start) tm
    | _, CodeNat ->
      Fmt.fprintf fmt "'nat"
    | `Pi, CodePi (base, fam) ->
      let x, env' = Pp.Env.bind env None in
      Format.fprintf fmt 
        "[%a : %a]@ %a" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go env' `Pi) fam
    | _, CodePi (base, fam) ->
      let x, envx = Pp.Env.bind env None in
      Format.fprintf fmt 
        "@[<hv1>('%a @[<hv>[%a : %a]@ %a@])@]" 
        Uuseg_string.pp_utf_8 "->" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go envx `Pi) fam
    | _, GoalRet tm ->
      Fmt.fprintf fmt "@[<hv1>(goal-ret %a)@]" (go env `Start) tm
    | _, GoalProj tm ->
      Fmt.fprintf fmt "@[<hv1>(goal-proj %a)@]" (go env `Start) tm
  in
  go env `Start

and pp_ghost_ env fmt ((name, cells), scrut) =
  let rec go_cells env fmt =
    function 
    | [] -> pp_ env fmt scrut
    | (_, tm) :: cells -> 
      Fmt.fprintf fmt "%a %a" (pp_ env) tm (go_cells env) cells
  in
  Fmt.fprintf fmt "@[<hv1>(%a %a)@]" pp_problem name (go_cells env) cells

and pp_problem fmt problem =
  let lbls = Bwd.to_list problem in
  let dot fmt () = Fmt.fprintf fmt "." in
  Fmt.pp_print_list ~pp_sep:dot Uuseg_string.pp_utf_8 fmt lbls


and pp_tp_ env = 
  let rec go env mode fmt tp = 
    match mode, tp with
    | `Pi, Pi (base, fam) ->
      let x, env' = Pp.Env.bind env None in
      Format.fprintf fmt 
        "[%a : %a]@ %a" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go env' `Pi) fam
    | _, Pi (base, fam) ->
      let x, envx = Pp.Env.bind env None in
      Format.fprintf fmt 
        "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" 
        Uuseg_string.pp_utf_8 "->" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go envx `Pi) fam
    | `Sg, Sg (base, fam) ->
      let x, env' = Pp.Env.bind env None in
      Format.fprintf fmt 
        "[%a : %a]@ %a" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go env' `Sg) fam
    | _, Sg (base, fam) ->
      let x, envx = Pp.Env.bind env None in
      Format.fprintf fmt 
        "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" 
        Uuseg_string.pp_utf_8 "*" 
        Uuseg_string.pp_utf_8 x 
        (go env `Start) base 
        (go envx `Pi) fam
    | _, Id (tp, l, r) ->
      Format.fprintf fmt 
        "@[<hv1>(Id@ %a@ %a@ %a)@]" 
        (go env `Start) tp 
        (pp_ env) l 
        (pp_ env) r
    | _, Nat ->
      Format.fprintf fmt "nat"
    | _, Univ ->
      Format.fprintf fmt "univ"
    | _, El tm ->
      Fmt.fprintf fmt "@[<hv1>(el@ %a)@]" (pp_ env) tm
    | _, GoalTp (None, tp) ->
      Fmt.fprintf fmt "@[<hv1>(goal@ _@ %a)@]" (pp_tp_ env) tp
    | _, GoalTp (Some lbl, tp) ->
      Fmt.fprintf fmt "@[<hv1>(goal@ ?%a@ %a)@]" 
        Uuseg_string.pp_utf_8 lbl 
        (pp_tp_ env) tp
  in
  go env `Start


let pp_sequent_goal env fmt =
  function
  | GoalTp (Some lbl, tp) ->
    Format.fprintf fmt "?%a : @[<hv>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp_ env) tp
  | GoalTp (None, tp) ->
    Format.fprintf fmt "@[<hv>%a@]"
      (pp_tp_ env) tp
  | tp ->
    pp_tp_ env fmt tp

let rec pp_sequent_inner ~names env fmt tp =
  match names, tp with
  | nm :: names, Pi (base, fam) ->
    let x, envx = Pp.Env.bind env @@ Some nm in
    Fmt.fprintf fmt "%a : %a@;%a"
      Uuseg_string.pp_utf_8 x
      (pp_tp_ env) base
      (pp_sequent_inner ~names envx) fam
  | _, tp ->
    Format.fprintf fmt "|- @[<hv>%a@]"
      (pp_sequent_goal env) tp

let pp_sequent ~names : tp Pp.printer =
  fun fmt tp ->
  Format.fprintf fmt "@[<v>%a@]"
    (pp_sequent_inner ~names Pp.Env.emp) tp

type env = tp list