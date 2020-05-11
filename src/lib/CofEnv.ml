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

let unreduced_assumptions env =
  env.cof


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
    | Cof.Cof phi ->
      begin
        match phi with
        | Cof.Eq (r, s) when r = s ->
          true
        | Cof.Eq (r, s) ->
          find_class local.classes r = find_class local.classes s
        | Cof.Join phis -> List.exists (right local) phis
        | Cof.Meet phis -> List.for_all (right local) phis
      end
    | Cof.Var v ->
      VarSet.mem v local.true_vars

  (* Invariant: classes is consistent *)
  let rec left local cx phi =
    match cx with
    | [] -> right local phi
    | Cof.Cof (Cof.Eq (r, s)) :: cx ->
      let classes = UF.union r s local.classes in
      if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
        true
      else
        left {local with classes} cx phi
    | Cof.Var v :: cx ->
      let local = {local with true_vars = VarSet.add v local.true_vars} in
      left local cx phi
    | Cof.Cof (Cof.Join psis) :: cx ->
      List.for_all (fun psi -> left local (psi :: cx) phi) psis
    | Cof.Cof (Cof.Meet psis) :: cx ->
      left local (psis @ cx) phi
end

let test env phi =
  match env.status with
  | `Inconsistent ->
    true
  | `Consistent ->
    let local = Inversion.{classes = env.classes; true_vars = env.true_vars} in
    Inversion.left local [env.cof] phi

let test_sequent (env : env) cx phi =
  let psi = Cof.meet cx in
  let local = Inversion.{classes = env.classes; true_vars = env.true_vars} in
  Inversion.left local [env.cof; psi] phi

let rec assume env phi =
  match env.status with
  | `Inconsistent -> env
  | `Consistent ->
    let phi = Cof.reduce phi in
    match phi with
    | Cof.Var v ->
      {env with true_vars = VarSet.add v env.true_vars}
    | Cof.Cof phi ->
      match phi with
      | Cof.Meet phis ->
        List.fold_left assume env phis
      | Cof.Join _ ->
        if test_sequent env [Cof.Cof phi] Cof.bot then inconsistent else
          {env with cof = Cof.meet [env.cof; Cof.Cof phi]}
      | Cof.Eq (r, s) ->
        let classes = UF.union r s env.classes in
        if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
          inconsistent
        else
          {env with classes}

let equate env r s =
  assume env @@ Cof.eq r s
