open Basis
open Cubical
open CodeUnit

module S = Syntax
module D = Domain
module RM = RefineMonad
module Sem = Semantics
module Qu = Quote

open Monad.Notation (RM)

let debug_tactic name =
  if String.length name = 0 then
    ()
  else
    Debug.print "Tactic: %s@." name

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
  val whnf : style:Semantics.whnf_style -> tac -> tac
end

module Tp : sig
  include Tactic

  val rule : ?name:string -> S.tp RM.m -> tac
  val virtual_rule : ?name:string -> S.tp RM.m -> tac

  val run : tac -> S.tp RM.m
  val run_virtual : tac -> S.tp RM.m
  val map : (S.tp RM.m -> S.tp RM.m) -> tac -> tac
end
=
struct
  type tac =
    | Virtual of string * S.tp RM.m
    | General of string * S.tp RM.m

  let rule ?(name = "") tac = General (name, tac)
  let virtual_rule ?(name = "") tac = Virtual (name, tac)

  let run =
    function
    | General (name, tac) ->
      debug_tactic name;
      tac
    | Virtual _ ->
      RM.refine_err @@ RefineError.VirtualType

  let run_virtual =
    function
    | General (name, tac)
    | Virtual (name, tac) ->
      debug_tactic name;
      tac

  let map f =
    function
    | General (name, tac) -> General (name, f tac)
    | Virtual (name, tac) -> Virtual (name, f tac)

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
  val chk : tac -> Chk.tac
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

  let chk v =
    Chk.syn @@ syn v

  let abstract : ?ident:Ident.t -> D.tp -> (Var.tac -> 'a RM.m) -> 'a RM.m =
    fun ?(ident = `Anon) tp kont ->
    RM.abstract ident tp @@ fun (con : D.con) ->
    kont @@ {tp; con}
end

and Chk : sig
  include Tactic

  val rule : ?name:string -> (D.tp -> S.t RM.m) -> tac
  val brule : ?name:string -> (D.tp * D.cof * D.tm_clo -> S.t RM.m) -> tac
  val run : tac -> D.tp -> S.t RM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t RM.m

  val syn : Syn.tac -> tac
end =
struct
  type tac =
    | Chk of string * (D.tp -> S.t RM.m)
    | BChk of string * (D.tp * D.cof * D.tm_clo -> S.t RM.m)

  let run =
    function
    | Chk (name, tac) ->
      debug_tactic name;
      tac
    | BChk (name, btac) ->
      debug_tactic name;
      fun tp ->
        let triv = D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp}) in
        btac (tp, Cof.bot, triv)

  let brun =
    function
    | Chk (name, tac) ->
      fun (tp, phi, clo) ->
        debug_tactic name;
        let* tm = tac tp in
        let* con = RM.lift_ev @@ Sem.eval tm in
        let* () =
          Var.abstract (D.TpPrf phi) @@ fun prf ->
          RM.equate tp con @<< RM.lift_cmp @@ Sem.inst_tm_clo clo @@ Var.con prf
        in
        RM.ret tm
    | BChk (name, btac) ->
      debug_tactic name;
      btac

  let rule ?(name = "") tac = Chk (name, tac)
  let brule ?(name = "") tac = BChk (name, tac)

  let update_span loc =
    function
    | Chk (name, tac) ->
      rule ~name @@ fun tp ->
      RM.update_span loc @@ tac tp
    | BChk (name, tac) ->
      brule ~name @@ fun goal ->
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
  val rule : ?name:string -> (S.t * D.tp) RM.m -> tac
  val run : tac -> (S.t * D.tp) RM.m
  val ann : Chk.tac -> Tp.tac -> tac
end =
struct
  type tac = string * (S.t * D.tp) RM.m

  let rule ?(name = "") tac = (name, tac)
  let run (name, tac) =
    debug_tactic name;
    tac

  let update_span loc (name, tac) =
    (name, RM.update_span loc tac)

  let ann (tac_tm : Chk.tac) (tac_tp : Tp.tac) : tac =
    rule @@
    let* tp = Tp.run tac_tp in
    let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
    let+ tm = Chk.run tac_tm vtp in
    tm, vtp

  let whnf ~style (name, tac) =
    rule ~name @@
    let* tm, tp = tac in
    RM.lift_cmp @@ Sem.whnf_tp ~style tp |>>
    function
    | `Done -> RM.ret (tm, tp)
    | `Reduce tp' -> RM.ret (tm, tp')
end

let abstract = Var.abstract

type var = Var.tac
