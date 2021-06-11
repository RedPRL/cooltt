open Basis
open Cubical
open CodeUnit

module S = Syntax
module D = Domain
module RM = RefineMonad
module Sem = Semantics
module Qu = Quote

open Monad.Notation (RM)

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
  val whnf : style:Semantics.whnf_style -> tac -> tac
end

module Tp : sig
  include Tactic

  val rule : S.tp RM.m -> tac
  val virtual_rule : S.tp RM.m -> tac

  val run : tac -> S.tp RM.m
  val run_virtual : tac -> S.tp RM.m
  val map : (S.tp RM.m -> S.tp RM.m) -> tac -> tac
end
=
struct
  type tac =
    | Virtual of S.tp RM.m
    | General of S.tp RM.m

  let rule tac = General tac
  let virtual_rule tac = Virtual tac

  let run =
    function
    | General tac -> tac
    | Virtual _ ->
      RM.refine_err @@ RefineError.VirtualType

  let run_virtual =
    function
    | General tac
    | Virtual tac -> tac

  let map f =
    function
    | General tac -> General (f tac)
    | Virtual tac -> Virtual (f tac)

  let update_span loc =
    map @@ RM.update_span loc

  let whnf ~style:_ tac =
    tac
end

module rec Var : sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> Syn.tac
  val abstract : ?ident:Ident.t -> D.tp -> (tac -> 'a RM.m) -> 'a RM.m
end =
struct
  type tac = {tp : D.tp; con : D.con}

  let prf phi = {tp = D.TpPrf phi; con = D.Prf}
  let con {tp = _; con} = con
  let syn {tp; con} =
    Syn.rule @@
    let+ tm = RM.quote_con tp con in
    tm, tp

  let abstract : ?ident:Ident.t -> D.tp -> (Var.tac -> 'a RM.m) -> 'a RM.m =
    fun ?(ident = `Anon) tp kont ->
    RM.abstract ident tp @@ fun (con : D.con) ->
    kont @@ {tp; con}
end

and Chk : sig
  include Tactic

  val rule : (D.tp -> S.t RM.m) -> tac
  val brule : (D.tp * D.cof * D.tm_clo -> S.t RM.m) -> tac
  val run : tac -> D.tp -> S.t RM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t RM.m

  val syn : Syn.tac -> tac
end =
struct
  type tac =
    | Chk of (D.tp -> S.t RM.m)
    | BChk of (D.tp * D.cof * D.tm_clo -> S.t RM.m)

  let run =
    function
    | Chk tac -> tac
    | BChk btac ->
      fun tp ->
        let triv = D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp}) in
        btac (tp, Cof.bot, triv)

  let brun =
    function
    | Chk tac ->
      fun (tp, phi, clo) ->
        let* tm = tac tp in
        let* con = RM.lift_ev @@ Sem.eval tm in
        let* () =
          Var.abstract (D.TpPrf phi) @@ fun prf ->
          RM.equate tp con @<< RM.lift_cmp @@ Sem.inst_tm_clo clo @@ Var.con prf
        in
        RM.ret tm
    | BChk btac -> btac

  let rule tac = Chk tac
  let brule tac = BChk tac

  let update_span loc =
    function
    | Chk tac ->
      rule @@ fun tp ->
      RM.update_span loc @@ tac tp
    | BChk tac ->
      brule @@ fun goal ->
      RM.update_span loc @@ tac goal

  let syn (tac : Syn.tac) : tac =
    rule @@ fun tp ->
    let* tm, tp' = Syn.run tac in
    let+ () = RM.equate_tp tp tp' in
    tm

  let whnf ~style tac =
    brule @@ fun (tp, phi, clo) ->
    RM.lift_cmp @@ Sem.whnf_tp ~style tp |>>
    function
    | `Done -> brun tac (tp, phi, clo)
    | `Reduce tp -> brun tac (tp, phi, clo)
end

and Syn : sig
  include Tactic
  val rule : (S.t * D.tp) RM.m -> tac
  val run : tac -> (S.t * D.tp) RM.m
  val ann : Chk.tac -> Tp.tac -> tac
end =
struct
  type tac = (S.t * D.tp) RM.m

  let rule tac = tac
  let run tac = tac

  let update_span loc =
    RM.update_span loc

  let ann (tac_tm : Chk.tac) (tac_tp : Tp.tac) : tac =
    let* tp = Tp.run tac_tp in
    let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
    let+ tm = Chk.run tac_tm vtp in
    tm, vtp

  let whnf ~style tac =
    let* tm, tp = tac in
    RM.lift_cmp @@ Sem.whnf_tp ~style tp |>>
    function
    | `Done -> RM.ret (tm, tp)
    | `Reduce tp' -> RM.ret (tm, tp')
end

let abstract = Var.abstract

type var = Var.tac
