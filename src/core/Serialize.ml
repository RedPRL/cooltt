open Cubical
open CodeUnit

module S = Syntax

module J = Ezjsonm

(* Basic JSON Helpers *)
let json_of_pair x y = `A [x; y]

let json_of_int n = `String (Int.to_string n)

let labeled lbl v = `A (`String lbl :: v)

(* Identitifers *)

let json_of_ident nm = `String (Ident.to_string nm)

let json_of_path path = `String (String.concat "." path)

(* FIXME: This doesn't work! A Global is basically just an index, so we need access to the state >:( *)
let json_of_global (sym : Global.t) : J.value = `String (Global.show sym)


(* Terms/Types *)

let rec json_of_tm =
  function
  | S.Var n -> labeled "var" [json_of_int n]
  | S.Global sym -> labeled "global" [json_of_global sym]
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
  | S.TpESub (sub, tp) -> labeled "sub" [json_of_sub sub; json_of_tp tp ]
  | S.TpLockedPrf tm -> labeled "locked" [json_of_tm tm]

and json_of_sign (sign : S.sign) : J.value =
  `O (List.map (fun (path, tp) -> (String.concat "." path, json_of_tp tp)) sign)

let json_of_ctx ctx : J.value =
  `O (List.map (fun (nm, tp) -> (Ident.to_string nm, json_of_tp tp)) ctx)

let serialize_goal (ctx : (Ident.t * S.tp) list) (tp : S.tp) : J.t =
  `O [ ("ctx", json_of_ctx ctx);
       ("goal", json_of_tp tp) ]
