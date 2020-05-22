module S := Syntax
module D := Domain

open Monads

val eval : S.t -> D.con evaluate
val eval_cof : S.t -> D.cof evaluate
val eval_tp : S.tp -> D.tp evaluate

type 'a whnf = [`Done | `Reduce of 'a]
val whnf_con : D.con -> D.con whnf compute
val whnf_cut : D.cut -> D.con whnf compute
val whnf_hd : D.hd -> D.con whnf compute
val whnf_tp : D.tp -> D.tp whnf compute

val normalize_cof : D.cof -> D.cof compute

val inst_tp_clo : D.tp_clo -> D.con -> D.tp compute
val inst_tm_clo : D.tm_clo -> D.con -> D.con compute

val do_ap : D.con -> D.con -> D.con compute
val do_ap2 : D.con -> D.con -> D.con -> D.con compute
val do_fst : D.con -> D.con compute
val do_snd : D.con -> D.con compute
val do_sub_out : D.con -> D.con compute
val do_el_out : D.con -> D.con compute
val unfold_el : D.con -> D.tp compute
val do_el : D.con -> D.tp compute
val do_goal_proj : D.con -> D.con compute

val con_to_dim : D.con -> D.dim compute
val con_to_cof : D.con -> D.cof compute
val cof_con_to_cof : (D.con, D.con) Cof.cof_f -> D.cof compute

val do_rigid_cap : D.dim -> D.dim -> D.cof -> D.con -> D.con -> D.con compute

val splice_tm : S.t Splice.t -> D.con compute
val splice_tp : S.tp Splice.t -> D.tp compute
