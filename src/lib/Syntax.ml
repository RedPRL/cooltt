open CoolBasis open Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int (* De Bruijn index *)

type cof = (int, dim) Cof.cof

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Global of Symbol.t
  | Let of t * t
  | Ann of t * tp
  | Zero
  | Suc of t
  | NatElim of ghost option * tp * t * t * t
  | Lam of t
  | Ap of t * t
  | DimLam of t
  | DimAp of t * dim
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | IdElim of ghost option * tp * t * t
  | GoalRet of t
  | GoalProj of t
  | Coe of t * dim * dim * t
  | HCom of t * dim * dim * cof * t
  | TpCode of t gtp
  | CofTree of cof_tree

and cof_tree = (int, dim, t) Cof.tree

and tp = Tp of tp gtp

and _ gtp =
  | Nat : 'a gtp
  | Pi : 'a * 'a -> 'a gtp
  | Sg : 'a * 'a -> 'a gtp
  | Id : 'a * t * t -> 'a gtp
  | DimPi : 'a -> 'a gtp
  | Univ : tp gtp
  | El : t -> tp gtp
  | GoalTp : string option * tp -> tp gtp


and ghost = string bwd * [`Con of (tp * t) | `Dim of dim | `Cof of cof] list

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
  | _, Var i -> 
    pp_var env fmt i
  | _, Global sym ->
    Symbol.pp fmt sym
  | _, Let (tm, bnd) ->
    let x, env' = Pp.Env.bind env None in
    Fmt.fprintf fmt 
      "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" 
      Uuseg_string.pp_utf_8 x 
      (pp env) tm 
      (pp env') bnd
  | _, Ann (tm, tp) ->
    Fmt.fprintf fmt "@[<hv1>(: @[<hov>%a@ %a@])@]" 
      (pp_tp env) tp 
      (pp env) tm
  | _, Coe (code, r, s, tm) ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hv1>(coe@ [%a] %a@ %a %a@ %a)@]"
      Uuseg_string.pp_utf_8 x 
      (pp env) code
      (pp_dim env) r 
      (pp_dim env) s
      (pp env) tm
  | _, HCom (code, r, s, phi, tm) ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hv1>(hcom@ %a@ %a %a@ %a@ [%a] %a)@]"
      (pp env) code
      (pp_dim env) r 
      (pp_dim env) s
      (Cof.pp_cof pp_var pp_dim env) phi
      Uuseg_string.pp_utf_8 x
      (pp envx) tm
  | _, Zero ->
    Fmt.fprintf fmt "0"
  | _, Suc tm ->
    begin
      match condense tm with 
      | Some n -> Fmt.fprintf fmt "%d" @@ n + 1
      | None -> Fmt.fprintf fmt "@[<hv1>(suc@ %a)@]" (pp env) tm
    end
  | _, NatElim (Some ghost, _, _, _, scrut) ->
    pp_ghost_ env mode fmt (ghost, scrut)
  | _, IdElim (Some ghost, _, _, scrut) ->
    pp_ghost_ env mode fmt (ghost, scrut)
  | _, NatElim (None, mot, zero, suc, scrut) ->
    let x, envx = Pp.Env.bind env None in
    let y, envxy = Pp.Env.bind envx None in
    Fmt.fprintf fmt
      "@[<hv1>(nat.elim@ [%a] %a @[<hv1>(zero@ %a)@]@ @[<hv1>(suc@ [%a %a] %a)@]@ %a)@]"
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
      "@[<hv1>(id.elim@ [%a %a %a] %a@ @[<hv1>(refl@ [%a] %a)@]@ %a@]"
      Uuseg_string.pp_utf_8 x
      Uuseg_string.pp_utf_8 y
      Uuseg_string.pp_utf_8 z
      (pp_tp envxyz) mot 
      Uuseg_string.pp_utf_8 x
      (pp envx) refl
      (pp env) scrut
  | `Lam, (Lam tm | DimLam tm) ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "[%a] %a" 
      Uuseg_string.pp_utf_8 x 
      (pp_ envx `Lam) tm
  | _, (Lam tm | DimLam tm) ->
    let x, envx = Pp.Env.bind env None in
    Fmt.fprintf fmt "@[<hv1>(lam@ [%a] %a)@]" 
      Uuseg_string.pp_utf_8 x 
      (pp_ envx `Lam) tm
  | _, Fst tm ->
    Fmt.fprintf fmt "@[<hv1>(fst@ %a)@]" (pp env) tm
  | _, Snd tm ->
    Fmt.fprintf fmt "@[<hv1>(snd@ %a)@]" (pp env) tm
  | `Ap, Ap (tm0, tm1) ->
    Fmt.fprintf fmt "%a@ %a" (pp_ env `Ap) tm0 (pp env) tm1
  | _, Ap (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hv1>(%a@ %a)@]" (pp_ env `Ap) tm0 (pp env) tm1
  | `Ap, DimAp (tm, tr) ->
    Fmt.fprintf fmt "%a@ %a" (pp_ env `Ap) tm (pp_dim env) tr
  | _, DimAp (tm, tr) ->
    Fmt.fprintf fmt "@[<hv1>(%a@ %a)@]" (pp_ env `Ap) tm (pp_dim env) tr
  | _, Pair (tm0, tm1) ->
    Fmt.fprintf fmt "@[<hv1>(pair@ %a@ %a)@]" (pp env) tm0 (pp env) tm1
  | _, Refl tm ->
    Fmt.fprintf fmt "@[<hv1>(refl %a)@]" (pp env) tm
  | _, GoalRet tm ->
    Fmt.fprintf fmt "@[<hv1>(goal-ret %a)@]" (pp env) tm
  | _, GoalProj tm ->
    Fmt.fprintf fmt "@[<hv1>(goal-proj %a)@]" (pp env) tm
  | _, TpCode gtp ->
    pp_gtp_ (fun env _ -> pp env) env `Start fmt gtp
  | _, CofTree tree ->
    Cof.pp_tree pp_var pp_dim pp env fmt tree

and pp_dim env fmt =
  function
  | Dim0 -> 
    Format.fprintf fmt "0"
  | Dim1 -> 
    Format.fprintf fmt "1"
  | DimVar i -> 
    Uuseg_string.pp_utf_8 fmt @@ Pp.Env.var i env

and pp env = pp_ env `Start

and pp_ghost_ env mode fmt ((name, cells), scrut) =
  let rec go_cells env fmt =
    function 
    | [] -> pp env fmt scrut
    | `Con (_, tm) :: cells -> 
      (* should that really be `Ap? *)
      Fmt.fprintf fmt "%a@ %a" (pp_ env `Ap) tm (go_cells env) cells
    | `Dim r :: cells -> 
      Fmt.fprintf fmt "%a@ %a" (pp_dim env) r (go_cells env) cells
    | `Cof phi :: cells -> 
      Fmt.fprintf fmt "%a@ %a" 
        (Cof.pp_cof pp_var pp_dim env) phi
        (go_cells env) cells
  in
  match mode with
  | `Ap ->
    Fmt.fprintf fmt "%a@ %a" pp_problem name (go_cells env) cells
  | _ ->
    Fmt.fprintf fmt "@[<hv1>(%a@ %a)@]" pp_problem name (go_cells env) cells

and pp_ghost env =
  pp_ghost_ env `Start

and pp_problem fmt problem =
  let lbls = Bwd.to_list problem in
  let dot fmt () = Fmt.fprintf fmt "." in
  Fmt.pp_print_list ~pp_sep:dot Uuseg_string.pp_utf_8 fmt lbls


and pp_gtp_ : type x. (Pp.env -> [`Start | `Pi | `Sg] -> x Pp.printer) -> Pp.env -> [`Start | `Pi | `Sg] -> x gtp Pp.printer = 
  fun go env mode fmt gtp -> 
  match mode, gtp with 
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
  | `Pi, DimPi fam -> 
    let x, env' = Pp.Env.bind env None in
    Format.fprintf fmt 
      "[%a : dim]@ %a" 
      Uuseg_string.pp_utf_8 x 
      (go env' `Pi) fam
  | _, DimPi fam ->
    let x, envx = Pp.Env.bind env None in
    Format.fprintf fmt 
      "@[<hv1>(%a @[<hv>[%a : dim]@ %a@])@]" 
      Uuseg_string.pp_utf_8 "->" 
      Uuseg_string.pp_utf_8 x 
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
      (pp env) l 
      (pp env) r
  | _, Nat ->
    Format.fprintf fmt "nat"
  | _, Univ ->
    Format.fprintf fmt "univ"
  | _, El tm ->
    Fmt.fprintf fmt "@[<hv1>(el@ %a)@]" (pp env) tm
  | _, GoalTp (None, tp) ->
    Fmt.fprintf fmt "@[<hv1>(goal@ _@ %a)@]" (go env `Start) tp
  | _, GoalTp (Some lbl, tp) ->
    Fmt.fprintf fmt "@[<hv1>(goal@ ?%a@ %a)@]" 
      Uuseg_string.pp_utf_8 lbl 
      (go env `Start) tp

and pp_tp_ (env : Pp.env) (mode : _) : tp Pp.printer = 
  fun fmt tp ->
  let Tp gtp = tp in
  pp_gtp_ pp_tp_ env mode fmt gtp

and pp_tp env = pp_tp_ env `Start

let pp_sequent_goal env fmt (Tp tp)  =
  match tp with
  | GoalTp (Some lbl, tp) ->
    Format.fprintf fmt "?%a : @[<hv>%a@]"
      Uuseg_string.pp_utf_8 lbl
      (pp_tp env) tp
  | GoalTp (None, tp) ->
    Format.fprintf fmt "@[<hv>%a@]"
      (pp_tp env) tp
  | tp ->
    pp_tp env fmt @@ Tp tp

let rec pp_sequent_inner ~names env fmt (Tp tp) =
  match names, tp with
  | nm :: names, Pi (base, fam) ->
    let x, envx = Pp.Env.bind env @@ Some nm in
    Fmt.fprintf fmt "%a : %a@;%a"
      Uuseg_string.pp_utf_8 x
      (pp_tp env) base
      (pp_sequent_inner ~names envx) fam
  | _, tp ->
    Format.fprintf fmt "|- @[<hv>%a@]"
      (pp_sequent_goal env) 
      (Tp tp)

let pp_sequent ~names : tp Pp.printer =
  fun fmt tp ->
  Format.fprintf fmt "@[<v>%a@]"
    (pp_sequent_inner ~names Pp.Env.emp) tp

type env = tp list