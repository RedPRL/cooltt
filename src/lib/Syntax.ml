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

let rec pp_ (env : Pp.env) fmt =
  function
  | Var i -> 
    Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var i env
  | Global sym ->
    Symbol.pp fmt sym
  | Let (tm, bnd) ->
    let x, env' = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" Uuseg_string.pp_utf_8 x (pp_ env) tm (pp_ env') bnd
  | Ann (tm, tp) ->
    Fmt.fprintf fmt "@[<hv1>(: @[<hov>%a@ %a@])@]" (pp_tp_ env) tp (pp_ env) tm
  | Zero ->
    Fmt.fprintf fmt "0"
  | Suc tm ->
    begin
      match condense tm with 
      | Some n -> Fmt.fprintf fmt "%d" @@ n + 1
      | None -> Fmt.fprintf fmt "@[<hv1>(suc@ %a)@]" (pp_ env) tm
    end
  | NatElim (mot, zero, suc, scrut) ->
    let x, envx = Pp.Env.bind env None in
    let y, envxy = Pp.Env.bind envx None in
    Fmt.fprintf  fmt
      "@[<hv1>(nat.elim [%a] %a @[<hv1>(zero@ %a)@]@ @[<hv1>(suc@ [%a %a] %a)@]@ %a)@]"
      Uuseg_string.pp_utf_8 x 
      (pp_tp_ envx) mot
      (pp_ env) zero
      Uuseg_string.pp_utf_8 x 
      Uuseg_string.pp_utf_8 y
      (pp_ envxy) suc
      (pp_ env) scrut
  | IdElim (mot, refl, scrut) ->
    let x, envx = Pp.Env.bind env None in
    let y, envxy = Pp.Env.bind envx None in
    let z, envxyz = Pp.Env.bind envxy None in
    Fmt.fprintf fmt
      "@[<hv1>(id.elim [%a %a %a] %a@ @[<hv1>(refl@ [%a] %a)@]@ %a@]"
      Uuseg_string.pp_utf_8 x
      Uuseg_string.pp_utf_8 y
      Uuseg_string.pp_utf_8 z
      (pp_tp_ envxyz) mot 
      Uuseg_string.pp_utf_8 x
      (pp_ envx) refl
      (pp_ env) scrut
  | Lam tm ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hv1>(lam@ [%a] %a)@]" Uuseg_string.pp_utf_8 x (pp_ envx) tm
  | Fst tm ->
    Fmt.fprintf fmt "@[<hv1>(fst@ %a)@]" (pp_ env) tm
  | Snd tm ->
    Fmt.fprintf fmt "@[<hv1>(snd@ %a)@]" (pp_ env) tm
  | Ap (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hv1>(%a@ %a)@]" (pp_ env) tm0 (pp_ env) tm1
  | Pair (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hv1>(pair@ %a@ %a)@]" (pp_ env) tm0 (pp_ env) tm1
  | Refl tm ->
    Fmt.fprintf fmt "@[<hv1>(refl %a)@]" (pp_ env) tm


and pp_tp_ env = 
  let rec go env mode fmt = 
    fun tp ->
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