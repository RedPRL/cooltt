open Cubical
open CodeUnit

module S = Syntax
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

let labeled lbl v = `A (`String lbl :: v)

(* Identitifers *)

let json_of_ident nm = `String (Ident.to_string nm)

(* FIXME: Machine names? *)
let json_to_ident : J.value -> Ident.t =
  function
  | `String "<anon>" -> `Anon
  | `String nm -> `User (String.split_on_char '.' nm)
  | j -> J.parse_error j "json_to_ident"

let json_of_path path = `String (String.concat "." path)

let json_to_path =
  function
  | `String path -> String.split_on_char '.' path
  | j -> J.parse_error j "json_to_path"

(* Terms/Types *)

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
  | S.Struct strct -> labeled "struct" [json_of_struct strct]
  | S.Proj (tm, path) -> labeled "proj" [json_of_tm tm; json_of_path path]
  | S.Coe (fam, src, trg, tm) -> labeled "coe" [json_of_tm fam; json_of_tm src; json_of_tm trg; json_of_tm tm]
  | S.HCom (code, src, trg, cof, tm) -> labeled "hcom" [json_of_tm code; json_of_tm src; json_of_tm trg; json_of_tm cof; json_of_tm tm]
  | S.Com (fam, src, trg, cof, tm) -> labeled "com" [json_of_tm fam; json_of_tm src; json_of_tm trg; json_of_tm cof; json_of_tm tm]
  | S.SubIn tm -> labeled "sub_in" [json_of_tm tm]
  | S.SubOut tm -> labeled "sub_out" [json_of_tm tm]
  | S.Dim0 -> `String "dim0"
  | S.Dim1 -> `String "dim1"
  | S.Cof cof -> labeled "cof" [json_of_cof cof]
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
  | S.CodeSignature sign -> labeled "code_sign" [json_of_struct sign]
  | S.CodeNat -> `String "code_nat"
  | S.CodeUniv -> `String "code_univ"
  | S.CodeV (r, pcode, code, pequiv) -> labeled "code_v" [json_of_tm r; json_of_tm pcode; json_of_tm code; json_of_tm pequiv]
  | S.CodeCircle -> `String "code_circle"
  | S.ESub (sb, tm) -> labeled "sub" [json_of_sub sb; json_of_tm tm]
  | S.LockedPrfIn tm -> labeled "prf_in" [json_of_tm tm]
  | S.LockedPrfUnlock {tp; cof; prf; bdy} -> labeled "prf_unlock" [json_of_tp tp; json_of_tm cof; json_of_tm prf; json_of_tm bdy]

and json_of_struct strct : J.value =
  `O (List.map (fun (path, tm) -> (String.concat "." path, json_of_tm tm)) strct)

and json_of_cof : (S.t, S.t) Cof.cof_f -> J.value =
  function
  | Eq (tm0, tm1) -> labeled "eq" [json_of_tm tm0; json_of_tm tm1]
  | Join tms -> labeled "join" @@ List.map json_of_tm tms
  | Meet tms -> labeled "meet" @@ List.map json_of_tm tms

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

and json_of_sign (sign : S.sign) : J.value =
  `O (List.map (fun (path, tp) -> (String.concat "." path, json_of_tp tp)) sign)

let json_of_ctx ctx : J.value =
  `O (List.map (fun (nm, tp) -> (Ident.to_string nm, json_of_tp tp)) ctx)

let serialize_goal (ctx : (Ident.t * S.tp) list) (tp : S.tp) : J.t =
  `O [ ("ctx", json_of_ctx ctx);
       ("goal", json_of_tp tp) ]

(* FIXME: None of this needs monadic context! *)
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
     let strct = json_to_struct j_strct in
     S.Struct strct
  | `A [`String "proj"; j_tm; j_path] ->
     let tm = json_to_tm j_tm in
     let path = json_to_path j_path in
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
     let cof = json_to_cof j_cof in
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
     let sign = json_to_struct j_sign in
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
  | j -> J.parse_error j "json_to_tm"

and json_to_struct : J.value -> (string list * S.t) list =
  function
  | `O j_strct -> j_strct |> List.map @@ fun (j_path, j_tm) ->
    let path = String.split_on_char '.' j_path in
    let tm = json_to_tm j_tm in
    (path, tm)
  | j -> J.parse_error j "json_to_struct"

and json_to_cof : J.value -> (S.t, S.t) Cof.cof_f =
  function
  | `A [`String "eq"; j_tm0; j_tm1] ->
     let tm0 = json_to_tm j_tm0 in
     let tm1 = json_to_tm j_tm1 in
     Cof.Eq (tm0, tm1)
  | `A (`String "join" :: j_tms) ->
     let tms = List.map json_to_tm j_tms in
     Cof.Join tms
  | `A (`String "meet" :: j_tms) ->
     let tms = List.map json_to_tm j_tms in
     Cof.Meet tms
  | j -> J.parse_error j "json_to_cof"
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
  | j -> J.parse_error j "json_to_sub"

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
     let sign = json_to_sign j_sign in
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
  | j -> J.parse_error j "json_to_tp"

and json_to_sign : J.value -> S.sign =
  function
  | `O j_sign -> j_sign |> List.map @@ fun (j_path, j_tp) ->
    let path = String.split_on_char '.' j_path in
    let tp = json_to_tp j_tp in
    (path, tp)
  | j -> J.parse_error j "json_to_sign"

let json_to_ctx : J.value -> (Ident.t * S.tp) list =
  function
  | `O j_ctx -> j_ctx |> List.map @@ fun (nm_str, j_tp) ->
    let nm = `User (String.split_on_char '.' nm_str) in
    let tp = json_to_tp j_tp in
    (nm, tp)
  | j -> J.parse_error j "json_to_ctx"

let deserialize_goal : J.t -> ((Ident.t * S.tp) list * S.tp) =
  function
  | `O [("ctx", j_ctx); ("goal", j_goal)] ->
     let ctx = json_to_ctx j_ctx in
     let goal = json_to_tp j_goal in
     (ctx, goal)
  | j -> J.parse_error (J.value j) "deserialize_goal"
