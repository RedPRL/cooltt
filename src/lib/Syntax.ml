open CoolBasis

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Global of Symbol.t
  | Let of t * (* BINDS *) t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of (* BINDS *) tp * t * (* BINDS 2 *) t * t
  | Lam of (* BINDS *) t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of (* BINDS 3 *) tp * (* BINDS *) t * t
[@@deriving show]

and tp =
  | Nat
  | Pi of tp * (* BINDS *) tp
  | Sg of tp * (* BINDS *) tp
  | Id of tp * t * t
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
  let rec go env mode fmt tm= 
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
    | _, NatElim (mot, zero, suc, scrut) ->
      let x, envx = Pp.Env.bind env None in
      let y, envxy = Pp.Env.bind envx None in
      Fmt.fprintf  fmt
        "@[<hv1>(nat.elim@ [%a] %a @[<hv1>(zero@ %a)@]@ @[<hv1>(suc@ [%a %a] %a)@]@ %a)@]"
        Uuseg_string.pp_utf_8 x 
        (pp_tp_ envx) mot
        (go env `Start) zero
        Uuseg_string.pp_utf_8 x 
        Uuseg_string.pp_utf_8 y
        (go envxy `Start) suc
        (go env `Start) scrut
    | _, IdElim (mot, refl, scrut) ->
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
  in
  go env `Start


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
      Format.fprintf fmt "Nat"
  in
  go env `Start

type env = tp list