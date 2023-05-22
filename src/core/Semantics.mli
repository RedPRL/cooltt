open Monads

open CodeUnit

module S := Syntax
module D := Domain

val eval : S.t -> D.con evaluate
val eval_cof : S.t -> D.cof evaluate
val eval_tp : S.tp -> D.tp evaluate
val eval_tele : S.tele -> D.tele evaluate

type 'a whnf = [`Done | `Reduce of 'a]
val whnf_con : D.con -> D.con whnf compute
val whnf_cut : D.cut -> D.con whnf compute
val whnf_hd : D.hd -> D.con whnf compute
val whnf_con_branches : (D.cof * D.tm_clo) list -> D.con whnf compute
val whnf_tp : D.tp -> D.tp whnf compute
val whnf_tp_branches : (D.cof * D.tp_clo) list -> D.tp whnf compute


val whnf_tp_ : D.tp -> D.tp compute
val whnf_con_ : D.con -> D.con compute

val inst_tp_clo : D.tp_clo -> D.con -> D.tp compute
val inst_tm_clo : D.tm_clo -> D.con -> D.con compute
val inst_tele_clo : D.tele_clo -> D.con -> D.tele compute
val inst_kan_tele_clo : D.kan_tele_clo -> D.con -> D.kan_tele compute
val inst_tele : D.tele -> D.con -> D.kan_tele compute
val inst_kan_tele : D.kan_tele -> D.con -> D.kan_tele compute


val do_ap : D.con -> D.con -> D.con compute
val do_ap2 : D.con -> D.con -> D.con -> D.con compute
val do_aps : D.con -> D.con list -> D.con compute
val do_fst : D.con -> D.con compute
val do_snd : D.con -> D.con compute
val do_proj : D.con -> Ident.t -> int -> D.con compute
val do_sub_out : D.con -> D.con compute
val do_el_out : D.con -> D.con compute
val unfold_el : D.con D.stable_code -> D.tp compute
val do_el : D.con -> D.tp compute
val do_spine : D.con -> D.frm list -> D.con compute

val con_to_dim : D.con -> D.dim compute
val con_to_cof : D.con -> D.cof compute
val cof_con_to_cof : (D.con, D.con) Kado.Syntax.endo -> D.cof compute

val do_rigid_cap : D.dim -> D.dim -> D.cof -> D.con -> D.con -> D.con compute
val do_rigid_vproj : D.dim -> D.con -> D.con -> D.con -> D.con -> D.con compute

(** Unpack a struct into a list of fields, potentially performing eta-expansion. *)
val do_unpack : D.tele -> D.con -> D.fields compute

val splice_tm : S.t Splice.t -> D.con compute
val splice_tp : S.tp Splice.t -> D.tp compute

val subst_con : D.dim -> DimProbe.t -> D.con -> D.con compute
val push_subst_con : D.dim -> DimProbe.t -> D.con -> D.con compute
