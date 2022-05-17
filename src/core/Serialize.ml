open Bwd
open CodeUnit

module S = Syntax
module D = Domain
module J = Ezjsonm

(* Basic JSON Helpers *)
let json_of_pair x y = `A [x; y]

let json_to_pair json_to_a json_to_b =
  function
  | `A [j_a; j_b] ->
    let a = json_to_a j_a in
    let b = json_to_b j_b in
    (a,b)
  | j -> J.parse_error j "json_to_pair"

let json_of_int n = `String (Int.to_string n)

let json_to_int : J.value -> int =
  function
  | `String n -> int_of_string n
  | j -> J.parse_error j "json_to_int"

let json_of_alist json_of_a json_of_b xs : J.value list =
  List.map (fun (a, b) -> json_of_pair (json_of_a a) (json_of_b b)) xs

let json_to_alist json_to_a json_to_b j_alist : ('a * 'b) list =
  List.map (json_to_pair json_to_a json_to_b) j_alist

let json_of_bwd json_of_el bwd : J.value =
  `A (BwdLabels.to_list @@ BwdLabels.map ~f:json_of_el bwd)

let json_to_bwd json_to_el : J.value -> 'a bwd =
  function
  | `A xs -> BwdLabels.map ~f:json_to_el @@ BwdLabels.of_list xs
  | j -> J.parse_error j "json_to_bwd"

let labeled lbl v = `A (`String lbl :: v)

(* Identitifers *)
let json_of_user =
  function
  | `User path -> `A (List.map J.string path)

let json_to_user : J.value -> [> `User of string list] =
  function
  | `A path -> `User (List.map J.get_string path)
  | j -> J.parse_error j "json_to_path"

let json_of_ident : Ident.t -> J.value =
  function
  | `Anon -> `String "anon"
  | `User _ as u -> `O [("user", json_of_user u)]
  | `Machine str -> `O [("machine", `String str)]

let json_to_ident : J.value -> Ident.t =
  function
  | `String "anon" -> `Anon
  | `O [("user", parts)] -> json_to_user parts
  | `O [("machine", `String str)] -> `Machine str
  | j -> J.parse_error j "json_to_ident"

let json_of_labeled json_of_el els : J.value =
  `O (List.map (fun (`User path, el) -> (String.concat "::" path, json_of_el el)) els)

let json_to_labeled json_to_el =
  function
  | `O j_els -> j_els |> List.map @@ fun (j_path, j_el) ->
    let path = CCString.split ~by:"::" j_path in
    let tm = json_to_el j_el in
    (`User path, tm)
  | j -> J.parse_error j "json_to_labeled"

module Cof =
struct
  module K = Kado.Syntax

  let json_of_cof_f (json_of_r : 'r -> J.value) (json_of_a : 'a -> J.value) : ('r, 'a) K.endo -> J.value =
    function
    | Eq (r0, r1) -> labeled "eq" [json_of_r r0; json_of_r r1]
    | Join xs -> labeled "join" @@ List.map json_of_a xs
    | Meet xs -> labeled "meet" @@ List.map json_of_a xs

  let rec json_of_cof (json_of_r : 'r -> J.value) (json_of_v : 'v -> J.value) : ('r, 'v) K.free -> J.value =
    function
    | Cof cof -> labeled "cof" [json_of_cof_f json_of_r (json_of_cof json_of_r json_of_v) cof]
    | Var v -> labeled "var" [json_of_v v]

  let json_to_cof_f (json_to_r : J.value -> 'r) (json_to_a : J.value -> 'a) : J.value -> ('r, 'a) K.endo =
    function
    | `A [`String "eq"; r0; r1] -> Eq (json_to_r r0, json_to_r r1)
    | `A (`String "join" :: xs) -> Join (List.map json_to_a xs)
    | `A (`String "meet" :: xs) -> Meet (List.map json_to_a xs)
    | j -> J.parse_error j "Cof.json_to_cof_f"

  let rec json_to_cof (json_to_r : J.value -> 'r) (json_to_v : J.value -> 'v) : J.value -> ('r, 'v) K.free =
    function
    | `A [`String "cof"; j_cof_f] -> Cof (json_to_cof_f json_to_r (json_to_cof json_to_r json_to_v) j_cof_f)
    | `A [`String "var"; j_var] -> Var (json_to_v j_var)
    | j -> J.parse_error j "Cof.json_to_cof"
end

(* Terms/Types *)
module Syntax =
struct

  let rec json_of_tm =
    function
    | S.Var n -> labeled "var" [json_of_int n]
    | S.Global sym -> labeled "global" [Global.serialize sym]
    | S.Let (tm, nm, body) -> labeled "let" [json_of_tm tm; json_of_ident nm; json_of_tm body]
    | S.Ann (tm, tp) -> labeled "ann" [json_of_tm tm; json_of_tp tp]
    | S.Zero -> `String "zero"
    | S.Suc tm -> labeled "suc" [json_of_tm tm]
    | S.NatElim (mot, zero, suc, scrut) -> labeled "nat_elim" [json_of_tm mot; json_of_tm zero; json_of_tm suc; json_of_tm scrut]
    | S.Base -> `String "base"
    | S.Loop tm -> labeled "loop" [json_of_tm tm]
    | S.CircleElim (mot, base, loop, scrut) -> labeled  "circle_elim" [json_of_tm mot; json_of_tm base; json_of_tm loop; json_of_tm scrut]
    | S.Lam (nm, body) -> labeled "lam" [json_of_ident nm; json_of_tm body]
    | S.Ap (tm0, tm1) -> labeled "ap" [json_of_tm tm0; json_of_tm tm1]
    | S.Pair (tm0, tm1) -> labeled "pair" [json_of_tm tm0; json_of_tm tm1]
    | S.Fst tm -> labeled "fst" [json_of_tm tm]
    | S.Snd tm -> labeled "snd" [json_of_tm tm]
    | S.Struct strct -> labeled "struct" [json_of_labeled json_of_tm strct]
    | S.Proj (tm, path) -> labeled "proj" [json_of_tm tm; json_of_user path]
    | S.Coe (fam, src, trg, tm) -> labeled "coe" [json_of_tm fam; json_of_tm src; json_of_tm trg; json_of_tm tm]
    | S.HCom (code, src, trg, cof, tm) -> labeled "hcom" [json_of_tm code; json_of_tm src; json_of_tm trg; json_of_tm cof; json_of_tm tm]
    | S.Com (fam, src, trg, cof, tm) -> labeled "com" [json_of_tm fam; json_of_tm src; json_of_tm trg; json_of_tm cof; json_of_tm tm]
    | S.SubIn tm -> labeled "sub_in" [json_of_tm tm]
    | S.SubOut tm -> labeled "sub_out" [json_of_tm tm]
    | S.Dim0 -> `String "dim0"
    | S.Dim1 -> `String "dim1"
    | S.Cof cof -> labeled "cof" [Cof.json_of_cof_f json_of_tm json_of_tm cof]
    | S.ForallCof cof -> labeled "forall" [json_of_tm cof]
    | S.CofSplit branches -> labeled "split" @@ List.map (fun (tphi, tm) -> json_of_pair (json_of_tm tphi) (json_of_tm tm)) branches
    | S.Prf -> `String "prf"
    | S.ElIn tm -> labeled "el_in" [json_of_tm tm]
    | S.ElOut tm -> labeled "el_out" [json_of_tm tm]
    | S.Box (r, s, phi, sides, cap) -> labeled "box" [json_of_tm r; json_of_tm s; json_of_tm phi; json_of_tm sides; json_of_tm cap]
    | S.Cap (r, s, phi, code, box) -> labeled "cap" [json_of_tm r; json_of_tm s; json_of_tm phi; json_of_tm code; json_of_tm box]
    | S.VIn (r, pequiv, pivot, base) -> labeled "v_in" [json_of_tm r; json_of_tm pequiv; json_of_tm pivot; json_of_tm base]
    | S.VProj (r, pcode, code, pequiv, v) -> labeled "v_proj" [json_of_tm r; json_of_tm pcode; json_of_tm code; json_of_tm pequiv; json_of_tm v]
    | S.CodeExt (n, fam, `Global phi, tbdry) -> labeled "code_ext" [json_of_int n; json_of_tm fam; json_of_tm phi; json_of_tm tbdry]
    | S.CodePi (tbase, tfam) -> labeled "code_pi" [json_of_tm tbase; json_of_tm tfam]
    | S.CodeSg (tbase, tfam) -> labeled "code_sg" [json_of_tm tbase; json_of_tm tfam]
    | S.CodeSignature sign -> labeled "code_sign" [json_of_labeled json_of_tm sign]
    | S.CodeNat -> `String "code_nat"
    | S.CodeUniv -> `String "code_univ"
    | S.CodeV (r, pcode, code, pequiv) -> labeled "code_v" [json_of_tm r; json_of_tm pcode; json_of_tm code; json_of_tm pequiv]
    | S.CodeCircle -> `String "code_circle"
    | S.ESub (sb, tm) -> labeled "sub" [json_of_sub sb; json_of_tm tm]
    | S.LockedPrfIn tm -> labeled "prf_in" [json_of_tm tm]
    | S.LockedPrfUnlock {tp; cof; prf; bdy} -> labeled "prf_unlock" [json_of_tp tp; json_of_tm cof; json_of_tm prf; json_of_tm bdy]

  and json_of_sub : S.sub -> J.value =
    function
    | S.SbI -> `String "id"
    | S.SbC (sb0, sb1) -> labeled "comp" [json_of_sub sb0; json_of_sub sb1]
    | S.Sb1 -> `String "1"
    | S.SbE (sb, tm) -> labeled "extend" [ json_of_sub sb; json_of_tm tm ]
    | S.SbP -> `String "proj"

  and json_of_tp : S.tp -> J.value =
    function
    | S.Univ -> `String "univ"
    | S.El tm -> labeled "el" [json_of_tm tm]
    | S.TpVar n -> labeled "var" [json_of_int n]
    | S.TpDim -> `String "dim"
    | S.TpCof -> `String "cof"
    | S.TpPrf tm -> labeled "prf" [json_of_tm tm]
    | S.TpCofSplit branches -> labeled "split" @@ List.map (fun (cof, tp) -> json_of_pair (json_of_tm cof) (json_of_tp tp)) branches
    | S.Sub (tp, tphi, tm) -> labeled "sub" [json_of_tp tp; json_of_tm tphi; json_of_tm tm]
    | S.Pi (base, nm, fib) -> labeled "pi" [json_of_tp base; json_of_ident nm; json_of_tp fib ]
    | S.Sg (base, nm, fib) -> labeled "sg" [json_of_tp base; json_of_ident nm; json_of_tp fib ]
    | S.Signature sign -> labeled "sign" [json_of_sign sign]
    | S.Nat -> `String "nat"
    | S.Circle -> `String "circle"
    | S.TpESub (sub, tp) -> labeled "subst" [json_of_sub sub; json_of_tp tp ]
    | S.TpLockedPrf tm -> labeled "locked" [json_of_tm tm]

  and json_of_sign : S.sign -> J.value =
    fun sign -> json_of_labeled json_of_tp sign

  let json_of_ctx ctx : J.value =
    `A (List.map (fun (nm, tp) -> json_of_pair (json_of_ident nm) (json_of_tp tp)) ctx)

  let rec json_to_tm : J.value -> S.t =
    function
    | `A [`String "var"; j_n] -> S.Var (json_to_int j_n)
    | `A [`String "global"; j_sym] ->
      let sym = Global.deserialize j_sym in
      S.Global sym
    | `A [`String "let"; j_tm; j_nm; j_body] ->
      let tm = json_to_tm j_tm in
      let nm = json_to_ident j_nm in
      let body = json_to_tm j_body in
      S.Let (tm, nm, body)
    | `A [`String "ann"; j_tm; j_tp] ->
      let tm = json_to_tm j_tm in
      let tp = json_to_tp j_tp in
      S.Ann (tm, tp)
    | `String "zero" -> S.Zero
    | `A [`String "suc"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.Suc tm
    | `A [`String "nat_elim"; j_mot; j_zero; j_suc; j_scrut] ->
      let mot = json_to_tm j_mot in
      let zero = json_to_tm j_zero in
      let suc = json_to_tm j_suc in
      let scrut = json_to_tm j_scrut in
      S.NatElim (mot, zero, suc, scrut)
    | `String "base" -> S.Base
    | `A [`String "loop"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.Loop tm
    | `A [`String "circle_elim"; j_mot; j_base; j_loop; j_scrut] ->
      let mot = json_to_tm j_mot in
      let base = json_to_tm j_base in
      let loop = json_to_tm j_loop in
      let scrut = json_to_tm j_scrut in
      S.CircleElim (mot, base, loop, scrut)
    | `A [`String "lam"; j_nm; j_body] ->
      let nm = json_to_ident j_nm in
      let body = json_to_tm j_body in
      S.Lam (nm, body)
    | `A [`String "ap"; j_tm0; j_tm1] ->
      let tm0 = json_to_tm j_tm0 in
      let tm1 = json_to_tm j_tm1 in
      S.Ap (tm0, tm1)
    | `A [`String "pair"; j_tm0; j_tm1] ->
      let tm0 = json_to_tm j_tm0 in
      let tm1 = json_to_tm j_tm1 in
      S.Pair (tm0, tm1)
    | `A [`String "fst"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.Fst tm
    | `A [`String "snd"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.Snd tm
    | `A [`String "struct"; j_strct] ->
      let strct = json_to_labeled json_to_tm j_strct in
      S.Struct strct
    | `A [`String "proj"; j_tm; j_path] ->
      let tm = json_to_tm j_tm in
      let path = json_to_user j_path in
      S.Proj (tm, path)
    | `A [`String "coe"; j_fam; j_src; j_trg; j_tm] ->
      let fam = json_to_tm j_fam in
      let src = json_to_tm j_src in
      let trg = json_to_tm j_trg in
      let tm = json_to_tm j_tm in
      S.Coe (fam, src, trg, tm)
    | `A [`String "hcom"; j_code; j_src; j_trg; j_cof; j_tm] ->
      let code = json_to_tm j_code in
      let src = json_to_tm j_src in
      let trg = json_to_tm j_trg in
      let cof = json_to_tm j_cof in
      let tm = json_to_tm j_tm in
      S.HCom (code, src, trg, cof, tm)
    | `A [`String "com"; j_fam; j_src; j_trg; j_cof; j_tm] ->
      let fam = json_to_tm j_fam in
      let src = json_to_tm j_src in
      let trg = json_to_tm j_trg in
      let cof = json_to_tm j_cof in
      let tm = json_to_tm j_tm in
      S.Com (fam, src, trg, cof, tm)
    | `A [`String "sub_in"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.SubIn tm
    | `A [`String "sub_out"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.SubOut tm
    | `String "dim0" -> S.Dim0
    | `String "dim1" -> S.Dim1
    | `A [`String "cof"; j_cof] ->
      let cof = Cof.json_to_cof_f json_to_tm json_to_tm j_cof in
      S.Cof cof
    | `A [`String "forall"; j_cof] ->
      let cof = json_to_tm j_cof in
      S.ForallCof cof
    | `A (`String "split" :: j_branches) ->
      let branches = List.map (json_to_pair json_to_tm json_to_tm) j_branches in
      S.CofSplit branches
    | `String "prf" -> S.Prf
    | `A [`String "el_in"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.ElIn tm
    | `A [`String "el_out"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.ElOut tm
    | `A [`String "box"; j_r; j_s; j_phi; j_sides; j_cap] ->
      let r = json_to_tm j_r in
      let s = json_to_tm j_s in
      let phi = json_to_tm j_phi in
      let sides = json_to_tm j_sides in
      let cap = json_to_tm j_cap in
      S.Box (r, s, phi, sides, cap)
    | `A [`String "cap"; j_r; j_s; j_phi; j_code; j_box] ->
      let r = json_to_tm j_r in
      let s = json_to_tm j_s in
      let phi = json_to_tm j_phi in
      let code = json_to_tm j_code in
      let box = json_to_tm j_box in
      S.Cap (r, s, phi, code, box)
    | `A [`String "v_in"; j_r; j_pequiv; j_pivot; j_base] ->
      let r = json_to_tm j_r in
      let pequiv = json_to_tm j_pequiv in
      let pivot = json_to_tm j_pivot in
      let base = json_to_tm j_base in
      S.VIn (r, pequiv, pivot, base)
    | `A [`String "v_proj"; j_r; j_pcode; j_code; j_pequiv; j_v] ->
      let r = json_to_tm j_r in
      let pcode = json_to_tm j_pcode in
      let code = json_to_tm j_code in
      let pequiv = json_to_tm j_pequiv in
      let v = json_to_tm j_v in
      S.VProj (r, pcode, code, pequiv, v)
    | `A [`String "code_ext"; j_n; j_fam; j_phi; j_bdry] ->
      let n = json_to_int j_n in
      let fam = json_to_tm j_fam in
      let phi = json_to_tm j_phi in
      let brdy = json_to_tm j_bdry in
      S.CodeExt (n, fam, `Global phi, brdy)
    | `A [`String "code_pi"; j_base; j_fam] ->
      let base = json_to_tm j_base in
      let fam = json_to_tm j_fam in
      S.CodePi (base, fam)
    | `A [`String "code_sg"; j_base; j_fam] ->
      let base = json_to_tm j_base in
      let fam = json_to_tm j_fam in
      S.CodeSg (base, fam)
    | `A [`String "code_sign"; j_sign] ->
      let sign = json_to_labeled json_to_tm j_sign in
      S.CodeSignature sign
    | `String "code_nat" -> S.CodeNat
    | `String "code_univ" -> S.CodeUniv
    | `A [`String "code_v"; j_r; j_pcode; j_code; j_pequiv] ->
      let r = json_to_tm j_r in
      let pcode = json_to_tm j_pcode in
      let code = json_to_tm j_code in
      let pequiv = json_to_tm j_pequiv in
      S.CodeV (r, pcode, code, pequiv)
    | `String "code_circle" -> S.CodeCircle
    | `A [`String "sub"; j_sb; j_tm] ->
      let sub = json_to_sub j_sb in
      let tm = json_to_tm j_tm in
      S.ESub (sub, tm)
    | `A [`String "prf_in"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.LockedPrfIn tm
    | `A [`String "prf_unlock"; j_tp; j_cof; j_prf; j_body] ->
      let tp = json_to_tp j_tp in
      let cof = json_to_tm j_cof in
      let prf = json_to_tm j_prf in
      let bdy = json_to_tm j_body in
      S.LockedPrfUnlock {tp; cof; prf; bdy}
    | j -> J.parse_error j "Syntax.json_to_tm"

  and json_to_sub : J.value -> S.sub =
    function
    | `String "id" -> S.SbI
    | `A [`String "comp"; j_sb0; j_sb1] ->
      let sb0 = json_to_sub j_sb0 in
      let sb1 = json_to_sub j_sb1 in
      S.SbC (sb0, sb1)
    | `String "1" -> S.Sb1
    | `A [`String "extend"; j_sb; j_tm] ->
      let sb = json_to_sub j_sb in
      let tm = json_to_tm j_tm in
      S.SbE (sb, tm)
    | `String "proj" -> S.SbP
    | j -> J.parse_error j "Syntax.json_to_sub"

  and json_to_tp : J.value -> S.tp =
    function
    | `String "univ" -> S.Univ
    | `A [`String "el"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.El tm
    | `A [`String "var"; j_n] ->
      let n = json_to_int j_n in
      S.TpVar n
    | `String "dim" -> S.TpDim
    | `String "cof" -> S.TpCof
    | `A [`String "prf"; j_prf] ->
      let prf = json_to_tm j_prf in
      S.TpPrf prf
    | `A (`String "split" :: j_branches) ->
      let branches = List.map (json_to_pair json_to_tm json_to_tp) j_branches in
      S.TpCofSplit branches
    | `A [`String "sub"; j_tp; j_tphi; j_tm] ->
      let tp = json_to_tp j_tp in
      let phi = json_to_tm j_tphi in
      let tm = json_to_tm j_tm in
      S.Sub (tp, phi, tm)
    | `A [`String "pi"; j_base; j_nm; j_fib] ->
      let base = json_to_tp j_base in
      let nm = json_to_ident j_nm in
      let fib = json_to_tp j_fib in
      S.Pi (base, nm, fib)
    | `A [`String "sg"; j_base; j_nm; j_fib] ->
      let base = json_to_tp j_base in
      let nm = json_to_ident j_nm in
      let fib = json_to_tp j_fib in
      S.Pi (base, nm, fib)
    | `A [`String "sign"; j_sign] ->
      let sign = json_to_labeled json_to_tp j_sign in
      S.Signature sign
    | `String "nat" -> S.Nat
    | `String "circle" -> S.Nat
    | `A [`String "subst"; j_sub; j_tp] ->
      let sub = json_to_sub j_sub in
      let tp = json_to_tp j_tp in
      S.TpESub (sub, tp)
    | `A [`String "locked"; j_tm] ->
      let tm = json_to_tm j_tm in
      S.TpLockedPrf tm
    | j -> J.parse_error j "Syntax.json_to_tp"

  and json_to_sign : J.value -> S.sign =
    fun j_sign -> json_to_labeled json_to_tp j_sign

  let json_to_ctx : J.value -> (Ident.t * S.tp) list =
    function
    | `A j_ctx -> j_ctx |> List.map @@ fun binding ->
      json_to_pair json_to_ident json_to_tp binding
    | j -> J.parse_error j "Syntax.json_to_ctx"
end

module Domain =
struct
  let rec json_of_con : D.con -> J.value =
    function
    | Lam (ident, clo) -> labeled "lam" [json_of_ident ident; json_of_tm_clo clo]
    | BindSym (dim_probe, con) -> labeled "bind_sym" [DimProbe.serialize dim_probe; json_of_con con]
    | LetSym (dim, dim_probe, con) -> labeled "let_sym" [json_of_dim dim; DimProbe.serialize dim_probe; json_of_con con]
    | Cut {tp; cut} -> labeled "cut" [json_of_tp tp; json_of_cut cut]
    | Zero -> `String "zero"
    | Suc con -> labeled "suc" [json_of_con con]
    | Base -> `String "base"
    | Loop dim -> labeled "loop" [json_of_dim dim]
    | Pair (con0, con1) -> labeled "pair" [json_of_con con0; json_of_con con1]
    | Struct fields -> labeled "struct" [json_of_labeled json_of_con fields]
    | SubIn con -> labeled "sub_in" [json_of_con con]
    | ElIn con -> labeled "el_in" [json_of_con con]
    | Dim0 -> `String "dim0"
    | Dim1 -> `String "dim1"
    | DimProbe dim_probe -> labeled "dim_probe" [DimProbe.serialize dim_probe]
    | Cof cof -> labeled "cof" [Cof.json_of_cof_f json_of_con json_of_con cof]
    | Prf -> `String "prf"
    | FHCom (tag, src, trg, cof, con) -> labeled "fhcom" [json_of_fhcom_tag tag; json_of_dim src; json_of_dim trg; json_of_cof cof; json_of_con con]
    | StableCode code -> labeled "stable_code" [json_of_stable_code code]
    | UnstableCode code -> labeled "unstable_code" [json_of_unstable_code code]
    | Box (src, trg, cof, sides, cap) -> labeled "box" [json_of_dim src; json_of_dim trg; json_of_cof cof; json_of_con sides; json_of_con cap]
    | VIn (s, eq, pivot, base) -> labeled "v_in" [json_of_dim s; json_of_con eq; json_of_con pivot; json_of_con base]
    | Split branches -> labeled "split" (json_of_alist json_of_cof json_of_tm_clo branches)
    | LockedPrfIn con -> labeled "locked_prf_in" [json_of_con con]

  and json_of_tm_clo : D.tm_clo -> J.value =
    function
    | Clo (tm, env) -> labeled "clo" [Syntax.json_of_tm tm; json_of_env env]

  and json_of_tp_clo : D.tp_clo -> J.value =
    function
    | Clo (tp, env) -> labeled "clo" [Syntax.json_of_tp tp; json_of_env env]

  and json_of_sign_clo : D.sign_clo -> J.value =
    function
    | Clo (sign, env) -> labeled "clo" [Syntax.json_of_sign sign; json_of_env env]

  and json_of_env {tpenv; conenv} : J.value =
    `O [("tpenv", json_of_bwd json_of_tp tpenv); ("conenv", json_of_bwd json_of_con conenv)]

  and json_of_cof (cof : D.cof) : J.value =
    Cof.json_of_cof json_of_dim json_of_int cof

  and json_of_dim : D.dim -> J.value =
    function
    | Dim0 -> `String "dim0"
    | Dim1 -> `String "dim1"
    | DimVar n -> labeled "dim_var" [json_of_int n]
    | DimProbe dim_probe -> labeled "dim_probe" [DimProbe.serialize dim_probe]

  and json_of_tp : D.tp -> J.value =
    function
    | Sub (tp, cof, clo) -> labeled "sub" [json_of_tp tp; json_of_cof cof; json_of_tm_clo clo]
    | Univ -> `String "univ"
    | ElCut cut -> labeled "el_cut" [json_of_cut cut]
    | ElStable code -> labeled "el_stable" [json_of_stable_code code]
    | ElUnstable code -> labeled "el_unstable" [json_of_unstable_code code]
    | TpDim -> `String "tp_dim"
    | TpCof -> `String "tp_cof"
    | TpPrf cof -> labeled "tp_prf" [json_of_cof cof]
    | TpSplit branches -> labeled "tp_split" (json_of_alist json_of_cof json_of_tp_clo branches)
    | Pi (tp, ident, clo) -> labeled "pi" [json_of_tp tp; json_of_ident ident; json_of_tp_clo clo]
    | Sg (tp, ident, clo) -> labeled "sg" [json_of_tp tp; json_of_ident ident; json_of_tp_clo clo]
    | Signature sign -> labeled "signature" [json_of_sign sign]
    | Nat -> `String "nat"
    | Circle -> `String "circle"
    | TpLockedPrf cof -> labeled "tp_locked_prf" [json_of_cof cof]

  and json_of_sign : D.sign -> J.value =
    function
    | D.Empty -> `String "empty"
    | D.Field (lbl, tp, clo) -> labeled "field" [json_of_user lbl; json_of_tp tp; json_of_sign_clo clo]

  and json_of_hd : D.hd -> J.value =
    function
    | D.Global sym -> labeled "global" [Global.serialize sym]
    | D.Var v -> labeled "var" [json_of_int v]
    | D.Coe (code, src, trg, con) -> labeled "coe" [json_of_con code; json_of_dim src; json_of_dim trg; json_of_con con]
    | D.UnstableCut (cut, frm) -> labeled "unstable_cut" [json_of_cut cut; json_of_unstable_frm frm]

  and json_of_frm : D.frm -> J.value =
    function
    | D.KAp (tp, con) -> labeled "k_ap" [json_of_tp tp; json_of_con con]
    | D.KFst -> `String "k_fst"
    | D.KSnd -> `String "k_snd"
    | D.KProj lbl -> labeled "k_proj" [json_of_user lbl]
    | D.KNatElim (mot, z, s) -> labeled "k_nat_elim" [json_of_con mot; json_of_con z; json_of_con s]
    | D.KCircleElim (mot, b, l) -> labeled "k_circle_elim" [json_of_con mot; json_of_con b; json_of_con l]
    | D.KElOut -> `String "k_el_out"

  and json_of_unstable_frm : D.unstable_frm -> J.value =
    function
    | D.KHCom (src, trg, cof, con) -> labeled "k_hcom" [json_of_dim src; json_of_dim trg; json_of_cof cof; json_of_con con]
    | D.KCap (src, trg, cof, con) -> labeled "k_cap" [json_of_dim src; json_of_dim trg; json_of_cof cof; json_of_con con]
    | D.KVProj (r, pcode, code, pequiv) -> labeled "k_vproj" [json_of_dim r; json_of_con pcode; json_of_con code; json_of_con pequiv]
    | D.KSubOut (cof, clo) -> labeled "k_sub_out" [json_of_cof cof; json_of_tm_clo clo]
    | D.KLockedPrfUnlock (tp, cof, con) -> labeled "k_locked_prf_unlock" [json_of_tp tp; json_of_cof cof; json_of_con con]

  and json_of_cut : D.cut -> J.value =
    fun (hd, frm) -> labeled "cut" (json_of_hd hd :: List.map json_of_frm frm)

  and json_of_stable_code : D.con D.stable_code -> J.value =
    function
    | `Pi (base, fam) -> labeled "pi" [json_of_con base; json_of_con fam]
    | `Sg (base, fam) -> labeled "sg" [json_of_con base; json_of_con fam]
    | `Signature sign -> labeled "signature" [json_of_labeled json_of_con sign]
    | `Ext (n, code, `Global phi, fam) -> labeled "ext" [json_of_int n; json_of_con code; json_of_con phi; json_of_con fam]
    | `Nat -> `String "nat"
    | `Circle -> `String "circle"
    | `Univ -> `String "univ"

  and json_of_unstable_code : D.con D.unstable_code -> J.value =
    function
    | `HCom (src, trg, cof, con) -> labeled "hcom" [json_of_dim src; json_of_dim trg; json_of_cof cof; json_of_con con]
    | `V (r, pcode, code, pequiv) -> labeled "v" [json_of_dim r; json_of_con pcode; json_of_con code; json_of_con pequiv]

  and json_of_fhcom_tag : [`Nat | `Circle] -> J.value =
    function
    | `Nat -> `String "nat"
    | `Circle -> `String "circle"

  let rec json_to_con : J.value -> D.con =
    function
    | `A [`String "lam"; j_ident; j_clo] -> Lam (json_to_ident j_ident, json_to_tm_clo j_clo)
    | `A [`String "bind_sym"; j_dim_probe; j_con] -> BindSym (DimProbe.deserialize j_dim_probe, json_to_con j_con)
    | `A [`String "let_sym"; j_dim; j_dim_probe; j_con] -> LetSym (json_to_dim j_dim, DimProbe.deserialize j_dim_probe, json_to_con j_con)
    | `A [`String "cut"; j_tp; j_cut] -> Cut {tp = json_to_tp j_tp; cut = json_to_cut j_cut}
    | `String "zero" -> Zero
    | `A [`String "suc"; j_con] -> Suc (json_to_con j_con)
    | `String "base" -> Base
    | `A [`String "loop"; j_dim] -> Loop (json_to_dim j_dim)
    | `A [`String "pair"; j_con0; j_con1] -> Pair (json_to_con j_con0, json_to_con j_con1)
    | `A [`String "struct"; j_fields] -> Struct (json_to_labeled json_to_con j_fields)
    | `A [`String "sub_in"; j_con] -> SubIn (json_to_con j_con)
    | `A [`String "el_in"; j_con] -> ElIn (json_to_con j_con)
    | `String "dim0" -> Dim0
    | `String "dim1" -> Dim1
    | `A [`String "dim_probe"; j_dim_probe] -> DimProbe (DimProbe.deserialize j_dim_probe)
    | `A [`String "cof"; j_cof] -> Cof (Cof.json_to_cof_f json_to_con json_to_con j_cof)
    | `String "prf" -> Prf
    | `A [`String "fhcom"; j_tag; j_src; j_trg; j_cof; j_con] -> FHCom (json_to_fhcom_tag j_tag, json_to_dim j_src, json_to_dim j_trg, json_to_cof j_cof, json_to_con j_con)
    | `A [`String "stable_code"; j_code] -> StableCode (json_to_stable_code j_code)
    | `A [`String "unstable_code"; j_code] -> UnstableCode (json_to_unstable_code j_code)
    | `A [`String "box"; j_src; j_trg; j_cof; j_sides; j_cap] -> Box (json_to_dim j_src, json_to_dim j_trg, json_to_cof j_cof, json_to_con j_sides, json_to_con j_cap)
    | `A [`String "v_in"; j_s; j_eq; j_pivot; j_base] -> VIn (json_to_dim j_s, json_to_con j_eq, json_to_con j_pivot, json_to_con j_base)
    | `A (`String "split" :: j_branches) -> Split (json_to_alist json_to_cof json_to_tm_clo j_branches)
    | `A [`String "locked_prf_in"; j_con] -> LockedPrfIn (json_to_con j_con)
    | j -> J.parse_error j "Domain.json_to_con"

  and json_to_tm_clo : J.value -> D.tm_clo =
    function
    | `A [`String "clo"; j_tm; j_env] -> Clo (Syntax.json_to_tm j_tm, json_to_env j_env)
    | j -> J.parse_error j "Domain.json_to_tm_clo"

  and json_to_tp_clo : J.value -> D.tp_clo =
    function
    | `A [`String "clo"; j_tp; j_env] -> Clo (Syntax.json_to_tp j_tp, json_to_env j_env)
    | j -> J.parse_error j "Domain.json_to_tp_clo"

  and json_to_sign_clo : J.value -> D.sign_clo =
    function
    | `A [`String "clo"; j_sign; j_env] -> Clo (Syntax.json_to_sign j_sign, json_to_env j_env)
    | j -> J.parse_error j "Domain.json_to_tp_clo"

  and json_to_env : J.value -> D.env =
    function
    | `O [("tpenv", j_tpenv); ("conenv", j_conenv)] ->
      { tpenv = json_to_bwd json_to_tp j_tpenv; conenv = json_to_bwd json_to_con j_conenv }
    | j -> J.parse_error j "Domain.json_to_env"

  and json_to_cof : J.value -> D.cof =
    fun j_cof -> Cof.json_to_cof json_to_dim json_to_int j_cof

  and json_to_dim : J.value -> D.dim =
    function
    | `String "dim0" -> Dim0
    | `String "dim1" -> Dim1
    | `A [`String "dim_var"; j_n] -> DimVar (json_to_int j_n)
    | `A [`String "dim_probe"; j_dim_probe] -> DimProbe (DimProbe.deserialize j_dim_probe)
    | j -> J.parse_error j "Domain.json_to_dim"

  and json_to_tp : J.value -> D.tp =
    function
    | `A [`String "sub"; j_tp; j_cof; j_clo] -> Sub (json_to_tp j_tp, json_to_cof j_cof, json_to_tm_clo j_clo)
    | `String "univ" -> Univ
    | `A [`String "el_cut"; j_cut] -> ElCut (json_to_cut j_cut)
    | `A [`String "el_stable"; j_code] -> ElStable (json_to_stable_code j_code)
    | `A [`String "el_unstable"; j_code] -> ElUnstable (json_to_unstable_code j_code)
    | `String "tp_dim" -> TpDim
    | `String "tp_cof" -> TpCof
    | `A [`String "tp_prf"; j_cof] -> TpPrf (json_to_cof j_cof)
    | `A (`String "tp_split" :: j_branches) -> TpSplit (json_to_alist json_to_cof json_to_tp_clo j_branches)
    | `A [`String "pi"; j_tp; j_ident; j_clo] -> Pi (json_to_tp j_tp, json_to_ident j_ident, json_to_tp_clo j_clo)
    | `A [`String "sg"; j_tp; j_ident; j_clo] -> Sg (json_to_tp j_tp, json_to_ident j_ident, json_to_tp_clo j_clo)
    | `A [`String "signature"; j_sign] -> Signature (json_to_sign j_sign)
    | `String "nat" -> Nat
    | `String "circle" -> Circle
    | `A [`String "tp_locked_prf"; j_cof] -> TpLockedPrf (json_to_cof j_cof)
    | j -> J.parse_error j "Domain.json_to_tp"

  and json_to_sign : J.value -> D.sign =
    function
    | `String "empty" -> Empty
    | `A [`String "field"; j_lbl; j_tp; j_clo] -> Field (json_to_user j_lbl, json_to_tp j_tp, json_to_sign_clo j_clo)
    | j -> J.parse_error j "Domain.json_to_sign"

  and json_to_hd : J.value -> D.hd =
    function
    | `A [`String "global"; j_sym] -> Global (Global.deserialize j_sym)
    | `A [`String "var"; j_n] -> Var (json_to_int j_n)
    | `A [`String "coe"; j_code; j_src; j_trg; j_con] -> Coe (json_to_con j_code, json_to_dim j_src, json_to_dim j_trg, json_to_con j_con)
    | `A [`String "unstable_cut"; j_cut; j_frm] -> UnstableCut (json_to_cut j_cut, json_to_unstable_frm j_frm)
    | j -> J.parse_error j "Domain.json_to_hd"

  and json_to_frm : J.value -> D.frm =
    function
    | `A [`String "k_ap"; j_tp; j_con] -> KAp (json_to_tp j_tp, json_to_con j_con)
    | `String "k_fst" -> KFst
    | `String "k_snd" -> KSnd
    | `A [`String "k_proj"; j_lbl] -> KProj (json_to_user j_lbl)
    | `A [`String "k_nat_elim"; j_mot; j_z; j_s] -> KNatElim (json_to_con j_mot, json_to_con j_z, json_to_con j_s)
    | `A [`String "k_circle_elim"; j_mot; j_b; j_l] -> KCircleElim (json_to_con j_mot, json_to_con j_b, json_to_con j_l)
    | `String "k-el_out" -> KElOut
    | j -> J.parse_error j "Domain.json_to_frm"

  and json_to_unstable_frm : J.value -> D.unstable_frm =
    function
    | `A [`String "k_hcom"; j_src; j_trg; j_cof; j_con] -> KHCom (json_to_dim j_src, json_to_dim j_trg, json_to_cof j_cof, json_to_con j_con)
    | `A [`String "k_cap"; j_src; j_trg; j_cof; j_con] -> KCap (json_to_dim j_src, json_to_dim j_trg, json_to_cof j_cof, json_to_con j_con)
    | `A [`String "k_vproj"; j_r; j_pcode; j_code; j_pequiv] -> KVProj (json_to_dim j_r, json_to_con j_pcode, json_to_con j_code, json_to_con j_pequiv)
    | `A [`String "k_sub_out"; j_cof; j_clo] -> KSubOut (json_to_cof j_cof, json_to_tm_clo j_clo)
    | `A [`String "k_locked_prf_unlock"; j_tp; j_cof; j_con] -> KLockedPrfUnlock (json_to_tp j_tp, json_to_cof j_cof, json_to_con j_con)
    | j -> J.parse_error j "Domain.json_to_unstable_frm"

  and json_to_cut : J.value -> D.cut =
    function
    | `A (`String "cut" :: j_hd :: j_frm) -> (json_to_hd j_hd, List.map json_to_frm j_frm)
    | j -> J.parse_error j "Domain.json_to_cut"

  and json_to_stable_code : J.value -> D.con D.stable_code =
    function
    | `A [`String "pi"; j_base; j_fam] -> `Pi (json_to_con j_base, json_to_con j_fam)
    | `A [`String "sg"; j_base; j_fam] -> `Sg (json_to_con j_base, json_to_con j_fam)
    | `A [`String "signature"; j_sign] -> `Signature (json_to_labeled json_to_con j_sign)
    | `A [`String "ext"; j_n; j_code; j_phi; j_fam] -> `Ext (json_to_int j_n, json_to_con j_code, `Global (json_to_con j_phi), json_to_con j_fam)
    | `String "nat" -> `Nat
    | `String "circle" -> `Circle
    | `String "univ" -> `Univ
    | j -> J.parse_error j "Domain.json_to_stable_code"

  and json_to_unstable_code : J.value -> D.con D.unstable_code =
    function
    | `A [`String "hcom"; j_src; j_trg; j_cof; j_con] -> `HCom (json_to_dim j_src, json_to_dim j_trg, json_to_cof j_cof, json_to_con j_con)
    | `A [`String "v"; j_r; j_pcode; j_code; j_pequiv] -> `V (json_to_dim j_r, json_to_con j_pcode, json_to_con j_code, json_to_con j_pequiv)
    | j -> J.parse_error j "Domain.json_to_unstable_code"

  and json_to_fhcom_tag : J.value -> [ `Nat | `Circle ] =
    function
    | `String "nat" -> `Nat
    | `String "circle" -> `Circle
    | j -> J.parse_error j "Domain.json_to_fhcom_tag"
end

let serialize_goal (ctx : (Ident.t * S.tp) list) (tp : S.tp) : J.t =
  `O [ ("ctx", Syntax.json_of_ctx ctx);
       ("goal", Syntax.json_of_tp tp) ]

let deserialize_goal : J.t -> ((Ident.t * S.tp) list * S.tp) =
  function
  | `O [("ctx", j_ctx); ("goal", j_goal)] ->
    let ctx = Syntax.json_to_ctx j_ctx in
    let goal = Syntax.json_to_tp j_goal in
    (ctx, goal)
  | j -> J.parse_error (J.value j) "deserialize_goal"

let serialize_bindings (bindings : (Ident.t * D.tp * D.con option) list) : J.t =
  `A (List.map (fun (nm, tp, con) -> `A [json_of_ident nm; Domain.json_of_tp tp; J.option Domain.json_of_con con]) bindings)

let deserialize_bindings : J.t -> (Ident.t * D.tp * D.con option) list =
  function
  | `A j_bindings -> j_bindings |> List.map @@
    begin
      function
      | `A [j_nm; j_tp; j_con] -> (json_to_ident j_nm, Domain.json_to_tp j_tp, J.get_option Domain.json_to_con j_con)
      | j -> J.parse_error j "deserialize_bindings"
    end
  | j -> J.parse_error (J.value j) "deserialize_bindings"
