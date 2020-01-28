open CoolBasis

module D = Domain
module UF = DisjointSet.Make (PersistentTable.M)

type env = 
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions *)

    cof : D.dim Cof.cof;
    (** a cofibration which is assumed true, but has not been eliminated yet *)

    status : [`Consistent | `Inconsistent]
    (** a cache which must be maintained *)
  }

let init () = 
  {classes = UF.init ~size:100;
   cof = Cof.top;
   status = `Consistent}

let inconsistent = 
  {classes = UF.init ~size:0;
   cof = Cof.bot;
   status = `Inconsistent}

let status env = env.status


let find_class classes r =
  try UF.find r classes with _ -> r


module Inversion =
struct
  let rec right classes =
    function
    | Cof.Eq (r, s) when r = s ->
      true
    | Cof.Eq (r, s) ->
      find_class classes r = find_class classes s
    | Cof.Join (phi0, phi1) ->
      if right classes phi0 then true else right classes phi1
    | Cof.Meet (phi0, phi1) ->
      if right classes phi0 then right classes phi1 else false
    | Cof.Bot -> false
    | Cof.Top -> true

  let rec left classes cx phi = 
    match cx with 
    | [] -> right classes phi
    | Cof.Eq (r, s) :: cx ->
      let classes = UF.union r s classes in
      if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
        true
      else
        left (UF.union r s classes) cx phi
    | Cof.Join (psi0, psi1) :: cx ->
      if left classes (psi0 :: cx) phi then left classes (psi1 :: cx) phi else false
    | Cof.Meet (psi0, psi1) :: cx -> 
      left classes (psi0 :: psi1 :: cx) phi
    | Cof.Top :: cx -> 
      left classes cx phi
    | Cof.Bot :: cx -> 
      true
end

let test env phi = 
  match env.status with 
  | `Inconsistent -> 
    true
  | `Consistent ->
    Inversion.left env.classes [env.cof] phi

let test_sequent env cx phi = 
  let psi = List.fold_left Cof.meet Cof.top cx in
  Inversion.left env.classes [env.cof; psi] phi

let rec assume env phi = 
  match env.status with 
  | `Inconsistent -> env
  | `Consistent -> 
    (* If the new assumption is stronger than what's on deck, throw the latter away *)
    let env = if test_sequent env [phi] env.cof then {env with cof = Cof.top} else env in
    match phi with 
    | Cof.Meet (phi0, phi1) -> 
      assume (assume env phi0) phi1
    | Cof.Join (_, _) -> 
      {env with cof = Cof.meet env.cof phi}
    | Cof.Top ->
      env 
    | Cof.Bot ->
      inconsistent
    | Cof.Eq (r, s) when r = s -> 
      env
    | Cof.Eq (r, s) ->
      let classes = UF.union r s env.classes in
      if UF.find D.Dim0 classes = UF.find D.Dim1 classes then 
        inconsistent
      else 
        {env with classes}

let equate env r s = 
  assume env @@ Cof.eq r s