module S = Syntax
module D = Domain
module EM = ElabBasics
module Sem = Semantics
module Qu = Quote

open Basis
open Cubical
open Monad.Notation (EM)

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
  val whnf : tac -> tac
end

module Tp : sig
  include Tactic

  val rule : S.tp EM.m -> tac
  val virtual_rule : S.tp EM.m -> tac

  val run : tac -> S.tp EM.m
  val run_virtual : tac -> S.tp EM.m
  val map : (S.tp EM.m -> S.tp EM.m) -> tac -> tac
end
=
struct
  type tac =
    | Virtual of S.tp EM.m
    | General of S.tp EM.m

  let rule tac = General tac
  let virtual_rule tac = Virtual tac

  let run =
    function
    | General tac -> tac
    | Virtual _ ->
      EM.elab_err @@ ElabError.VirtualType

  let run_virtual =
    function
    | General tac
    | Virtual tac -> tac

  let map f =
    function
    | General tac -> General (f tac)
    | Virtual tac -> Virtual (f tac)

  let update_span loc =
    map @@ EM.update_span loc

  let whnf tac = tac
end

module rec Var : sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> Syn.tac
  val abstract : ?ident:Ident.t -> D.tp -> (tac -> 'a EM.m) -> 'a EM.m
end =
struct
  type tac = {tp : D.tp; con : D.con}

  let prf phi = {tp = D.TpPrf phi; con = D.Prf}
  let con {tp = _; con} = con
  let syn {tp; con} =
    Syn.rule @@
    let+ tm = EM.quote_con tp con in
    tm, tp

  let abstract : ?ident:Ident.t -> D.tp -> (Var.tac -> 'a EM.m) -> 'a EM.m =
    fun ?(ident = `Anon) tp kont ->
    EM.abstract ident tp @@ fun (con : D.con) ->
    kont @@ {tp; con}
end

and Chk : sig
  include Tactic

  val rule : (D.tp -> S.t EM.m) -> tac
  val brule : (D.tp * D.cof * D.tm_clo -> S.t EM.m) -> tac
  val run : tac -> D.tp -> S.t EM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t EM.m

  val bchk : Chk.tac -> tac
  val syn : Syn.tac -> tac
end =
struct
  type tac =
    | Chk of (D.tp -> S.t EM.m)
    | BChk of (D.tp * D.cof * D.tm_clo -> S.t EM.m)

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
        let* con = EM.lift_ev @@ Sem.eval tm in
        let* () =
          Var.abstract (D.TpPrf phi) @@ fun prf ->
          EM.equate tp con @<< EM.lift_cmp @@ Sem.inst_tm_clo clo @@ Var.con prf
        in
        EM.ret tm
    | BChk btac -> btac

  let rule tac = Chk tac
  let brule tac = BChk tac
  let make tac = Chk tac

  let update_span loc =
    function
    | Chk tac ->
      rule @@ fun tp ->
      EM.update_span loc @@ tac tp
    | BChk tac ->
      brule @@ fun goal ->
      EM.update_span loc @@ tac goal

  let bchk : Chk.tac -> tac =
    fun btac ->
    brule @@ Chk.brun btac

  let syn (tac : Syn.tac) : tac =
    rule @@ fun tp ->
    let* tm, tp' = Syn.run tac in
    let+ () = EM.equate_tp tp tp' in
    tm

  let whnf tac =
    rule @@
    fun tp ->
    EM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> run tac tp
    | `Reduce tp -> run tac tp
end

and Syn : sig
  include Tactic
  val rule : (S.t * D.tp) EM.m -> tac
  val run : tac -> (S.t * D.tp) EM.m
  val ann : Chk.tac -> Tp.tac -> tac
end =
struct
  type tac = (S.t * D.tp) EM.m

  let rule tac = tac
  let run tac = tac

  let update_span loc =
    EM.update_span loc

  let ann (tac_tm : Chk.tac) (tac_tp : Tp.tac) : tac =
    let* tp = Tp.run tac_tp in
    let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
    let+ tm = Chk.run tac_tm vtp in
    tm, vtp

  let whnf tac =
    let* tm, tp = tac in
    EM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> EM.ret (tm, tp)
    | `Reduce tp' -> EM.ret (tm, tp')
end

let abstract = Var.abstract

type var = Var.tac
