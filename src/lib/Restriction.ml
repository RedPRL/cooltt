open CoolBasis

module D = Domain

type dim = D.dim

module UF = DisjointSet.Make (PersistentTable.M)

type t =
  {classes : dim UF.t;
   size : int}

let emp () =
  {classes = UF.init ~size:100;
   size = 0}

let equate_ t r r' =
  {classes = UF.union r r' t.classes;
   size = t.size + 1}

exception Inconsistent 

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let canonize r t =
  let rr = find r t in
  let res =
    if rr = find D.Dim0 t then
      D.Dim0
    else if rr = find D.Dim1 t then
      D.Dim1
    else
      rr
  in
  (* Format.printf "%a |= 0 ==> %a@." pp t D.pp_repr (find D.Dim0 t);
     Format.printf "Canonizing %a in %a as %a@." D.pp_repr r pp t D.pp_repr res; *)
  res

let compare t r r' =
  let cr = canonize r t in
  let cr' = canonize r' t in
  match cr, cr' with 
  | D.Dim0, D.Dim0 -> `Same
  | D.Dim1, D.Dim1 -> `Same
  | D.Dim0, D.Dim1 -> `Apart
  | D.Dim1, D.Dim0 -> `Apart
  | D.DimVar l0, DimVar l1 when l0 = l1 -> `Same
  | _ -> `Indet


let equate t r0 r1 =
  let t' = equate_ t r0 r1 in
  begin
    match compare t' D.Dim0 D.Dim1 with
    | `Same ->
      raise Inconsistent
    | _ -> ()
  end;
  t'

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

let test_sequent (t : t) (cx : _ list) (psi : dim Cof.cof) =
  let rec go (t : t) (cx : _ list) (psi : dim Cof.cof) =
    match cx with
    | [] -> test_cof t psi
    | Cof.Eq (r, s) :: cx -> 
      let t' = equate t r s in
      go t' cx psi
    | Cof.Join (phi0, phi1) :: cx -> 
      if go t (phi0 :: cx) psi then go t (psi :: cx) psi else false
    | Cof.Meet (phi0, phi1) :: cx -> 
      go t (phi0 :: phi1 :: cx) psi
    | Cof.Bot :: cx -> 
      true
    | Cof.Top :: cx ->
      go t cx psi
  in 
  try go t cx psi with 
  | Inconsistent -> 
    true

(* poor man's tests *)
let _  =
  try
    let x = D.DimVar 0 in
    let rst = equate (emp ()) x D.Dim1 in
    let _rst = equate rst x D.Dim0  in
    failwith "Test failed"
  with
  | Inconsistent -> ()

let _ =
  let x = D.DimVar 0 in
  let rst = equate (emp ()) x D.Dim0 in
  assert (canonize x rst = D.Dim0)