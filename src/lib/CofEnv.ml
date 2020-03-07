open CoolBasis

module D = Domain
module UF = DisjointSet.Make (PersistentTable.M)
module VarSet = Set.Make (Int)

type env = 
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions *)

    cof : D.cof;
    (** a cofibration which is assumed true, but has not been eliminated yet *)

    status : [`Consistent | `Inconsistent];
    (** a cache which must be maintained *)

    true_vars : VarSet.t
  }

let init () = 
  {classes = UF.init ~size:100;
   true_vars = VarSet.empty;
   cof = Cof.top;
   status = `Consistent}

let inconsistent = 
  {classes = UF.init ~size:0;
   cof = Cof.bot;
   true_vars = VarSet.empty;
   status = `Inconsistent}

let status env = env.status

let find_class classes r =
  try UF.find r classes with _ -> r


module Inversion :
sig 
  type local = 
    {classes : D.dim UF.t;
     true_vars : VarSet.t}

  val left : local -> D.cof list -> D.cof -> bool
end =
struct
  type local = 
    {classes : D.dim UF.t;
     true_vars : VarSet.t}

  (* Invariant: classes is consistent *)
  let rec right local =
    function
    | Cof.Eq (r, s) when r = s ->
      true
    | Cof.Eq (r, s) ->
      find_class local.classes r = find_class local.classes s
    | Cof.Join (phi0, phi1) ->
      if right local phi0 then true else right local phi1
    | Cof.Meet (phi0, phi1) ->
      if right local phi0 then right local phi1 else false
    | Cof.Bot -> false
    | Cof.Top -> true
    | Cof.Var v -> 
      VarSet.mem v local.true_vars 

  (* Invariant: classes is consistent *)
  let rec left local cx phi = 
    match cx with 
    | [] -> right local phi
    | Cof.Eq (r, s) :: cx ->
      let classes = UF.union r s local.classes in
      if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
        true
      else
        left {local with classes} cx phi
    | Cof.Var v :: cx ->
      let local = {local with true_vars = VarSet.add v local.true_vars} in
      left local cx phi
    | Cof.Join (psi0, psi1) :: cx ->
      if left local (psi0 :: cx) phi then left local (psi1 :: cx) phi else false
    | Cof.Meet (psi0, psi1) :: cx -> 
      left local (psi0 :: psi1 :: cx) phi
    | Cof.Top :: cx -> 
      left local cx phi
    | Cof.Bot :: cx -> 
      true
end

let test env phi = 
  match env.status with 
  | `Inconsistent -> 
    true
  | `Consistent ->
    let local = Inversion.{classes = env.classes; true_vars = env.true_vars} in
    Inversion.left local [env.cof] phi

let test_sequent (env : env) cx phi = 
  let psi = List.fold_left Cof.meet Cof.top cx in
  let local = Inversion.{classes = env.classes; true_vars = env.true_vars} in
  Inversion.left local [env.cof; psi] phi

let rec assume env phi = 
  match env.status with 
  | `Inconsistent -> env
  | `Consistent -> 
    let phi = Cof.reduce phi in
    (* If the new assumption is stronger than what's on deck, throw the latter away *)
    let env = if test_sequent env [phi] env.cof then {env with cof = Cof.top} else env in
    match phi with 
    | Cof.Bot ->
      inconsistent
    | Cof.Top ->
      env
    | Cof.Meet (phi0, phi1) -> 
      assume (assume env phi0) phi1
    | Cof.Join _ -> 
      if test_sequent env [phi] Cof.bot then inconsistent else
        {env with cof = Cof.meet env.cof phi}
    | Cof.Eq (r, s) ->
      let classes = UF.union r s env.classes in
      if UF.find D.Dim0 classes = UF.find D.Dim1 classes then 
        inconsistent
      else 
        {env with classes}
    | Cof.Var v -> 
      {env with true_vars = VarSet.add v env.true_vars}

let equate env r s = 
  assume env @@ Cof.eq r s