open Basis

type shift = {init: int; steps: int list}

let id_shift = {init = 0; steps = []}

let rec lt_iterated s i =
  match s.steps with
  | [] -> s.init < i
  | step :: steps -> lt_iterated {init = s.init + step; steps} (i + 1)

let rec leq_iterated s i =
  match s.steps with
  | [] -> s.init <= i
  | step :: steps -> leq_iterated {init = s.init + step; steps} (i + 1)

let equal_shift s0 s1 = s0 = s1 (* XXX poly eq *)

let rec lt_shift s0 s1 =
  s0.init < s1.init &&
  match s0.steps, s1.steps with
  | [], _ -> true (* this is sufficient because a step >= 1 *)
  | _, [] -> lt_iterated s0 s1.init
  | g0 :: steps0, g1 :: steps1 ->
    lt_shift {init = s0.init + g0; steps = steps0} {init = s1.init + g1; steps = steps1}

let rec leq_shift s0 s1 =
  s0.init <= s1.init &&
  match s0.steps, s1.steps with
  | [], _ -> true (* this is sufficient because a step >= 1 *)
  | _, [] -> leq_iterated s0 s1.init
  | g0 :: steps0, g1 :: steps1 ->
    leq_shift {init = s0.init + g0; steps = steps0} {init = s1.init + g1; steps = steps1}

type t =
  | LvlShiftedVar of {var: int; shift: shift}
  | LvlShiftedGlobal of {sym: Symbol.t; shift: shift}
  | LvlMagic
  | LvlTop

let magic = LvlMagic

let var i = LvlShiftedVar {var = i; shift = id_shift}

let global sym = LvlShiftedGlobal {sym; shift = id_shift}

let equal x y =
  match x, y with
  | LvlShiftedGlobal {sym = sym0; shift = shift0},
    LvlShiftedGlobal {sym = sym1; shift = shift1} ->
    Symbol.equal sym0 sym1 && equal_shift shift0 shift1
  | _ -> x = y || x = LvlMagic || y = LvlMagic

let lt x y =
  match x, y with
  | LvlMagic, _ -> true
  | _, LvlMagic -> true
  | (LvlShiftedVar _ | LvlShiftedGlobal _), LvlTop -> true
  | LvlShiftedVar {var = var0; shift = shift0},
    LvlShiftedVar {var = var1; shift = shift1} ->
    var0 = var1 && lt_shift shift0 shift1
  | LvlShiftedGlobal {sym = sym0; shift = shift0},
    LvlShiftedGlobal {sym = sym1; shift = shift1} ->
    Symbol.equal sym0 sym1 && lt_shift shift0 shift1
  | _ -> false

let leq x y =
  equal x y || lt x y

let rec compose_init s init1 =
  match s.steps, init1 with
  | _, 0 -> s
  | [], _ -> {init = s.init + init1; steps = []}
  | step :: steps, _ ->
    compose_init {init = s.init + step; steps} (init1-1)

let rec compose_steps steps steps1 =
  match steps, steps1 with
  | _, [] -> steps
  | [], _ -> steps1
  | init :: steps, step1 :: steps1 ->
    let {init; steps} = compose_init {init; steps} step1 in
    init :: compose_steps steps steps1

let compose_shift s0 s1 =
  let {init; steps} = compose_init s0 s1.init in
  let steps = compose_steps steps s1.steps in
  {init; steps}

let apply s l =
  match l with
  | LvlMagic | LvlTop -> l
  | LvlShiftedVar {var; shift} -> LvlShiftedVar {var; shift = compose_shift shift s}
  | LvlShiftedGlobal {sym; shift} -> LvlShiftedGlobal {sym; shift = compose_shift shift s}

let pp_shift fmt {init; steps} =
  Format.fprintf fmt "{%i;" init;
  List.iter (fun step -> Format.fprintf fmt "+%i;" step) steps;
  Format.pp_print_string fmt "...}"
