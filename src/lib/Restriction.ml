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

let equate_ r r' t =
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

let compare r r' t =
  let cr = canonize r t in
  let cr' = canonize r' t in
  match cr, cr' with 
  | D.Dim0, D.Dim0 -> `Same
  | D.Dim1, D.Dim1 -> `Same
  | D.Dim0, D.Dim1 -> `Apart
  | D.Dim1, D.Dim0 -> `Apart
  | D.DimVar l0, DimVar l1 when l0 = l1 -> `Same
  | _ -> `Indet


let equate r0 r1 t =
  let res = equate_ r0 r1 t in
  begin
    match compare D.Dim0 D.Dim1 res with
    | `Same ->
      raise Inconsistent
    | _ -> ()
  end;
  res

(* poor man's tests *)
let _  =
  try
    let x = D.DimVar 0 in
    let rst = equate x D.Dim1 @@ emp () in
    let _rst = equate x D.Dim0 rst in
    failwith "Test failed"
  with
  | Inconsistent -> ()

let _ =
  let x = D.DimVar 0 in
  let rst = equate x D.Dim0 @@ emp () in
  assert (canonize x rst = D.Dim0)