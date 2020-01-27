open CoolBasis

module D = Domain
module UF = DisjointSet.Make (PersistentTable.M)

type dim = D.dim

type t =
  {classes : dim UF.t}

let emp () =
  {classes = UF.init ~size:100}

let equate t r r' =
  {classes = UF.union r r' t.classes}

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let equal t r0 r1 =
  find r0 t = find r1 t

let rec test_cof t =
  function
  | Cof.Eq (r, s) ->
    equal t r s
  | Cof.Join (phi0, phi1) ->
    if test_cof t phi0 then true else test_cof t phi1
  | Cof.Meet (phi0, phi1) ->
    if test_cof t phi0 then test_cof t phi1 else false
  | Cof.Bot ->
    equal t D.Dim0 D.Dim1
  | Cof.Top -> 
    true

let status t =
  if equal t D.Dim0 D.Dim1 then 
    `Inconsistent 
  else 
    `Consistent

let test_sequent (t : t) (cx : _ list) (psi : dim Cof.cof) =
  let rec go (t : t) (cx : _ list) (psi : dim Cof.cof) =
    match cx with
    | [] -> test_cof t psi
    | Cof.Eq (r, s) :: cx -> 
      let t' = equate t r s in
      begin
        match status t' with 
        | `Inconsistent -> true 
        | `Consistent -> go t' cx psi
      end
    | Cof.Join (phi0, phi1) :: cx -> 
      if go t (phi0 :: cx) psi then go t (psi :: cx) psi else false
    | Cof.Meet (phi0, phi1) :: cx -> 
      go t (phi0 :: phi1 :: cx) psi
    | Cof.Bot :: cx -> 
      true
    | Cof.Top :: cx ->
      go t cx psi
  in 
  go t cx psi