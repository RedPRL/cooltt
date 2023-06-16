open Basis
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
  val whnf : tac -> tac
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

  let whnf tac =
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
    fun ?(ident = Ident.anon) tp kont ->
    RM.abstract ident tp @@ fun (con : D.con) ->
    kont @@ {tp; con}
end

and Chk : sig
  include Tactic

  val rule : ?name:string -> (D.tp -> S.t RM.m) -> tac
  val brule : ?name:string -> (D.tp * D.cof * D.tm_clo -> S.t RM.m) -> tac
  val run : tac -> D.tp -> S.t RM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t RM.m

  val catch : tac -> (exn -> tac) -> tac

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
        btac (tp, CofBuilder.bot, triv)

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
      fun (tp, phi, clo) ->
        debug_tactic name;
        btac (tp, phi, clo)

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

  let catch tac handle : tac =
    brule @@ fun (tp, phi, clo) ->
    let* st = RM.get in
    let* r = RM.trap @@ brun tac (tp, phi, clo) in
    match r with
    | Ok s -> RM.ret s
    | Error exn ->
      let* () = RM.set st in
      brun (handle exn) (tp, phi, clo)

  let whnf tac =
    brule @@ fun (tp, phi, clo) ->
    RM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> brun tac (tp, phi, clo)
    | `Reduce tp -> brun tac (tp, phi, clo)
end

and Syn : sig
  include Tactic
  val rule : ?name:string -> (S.t * D.tp) RM.m -> tac
  val run : tac -> (S.t * D.tp) RM.m
  val ann : Chk.tac -> Tp.tac -> tac

  val catch : tac -> (exn -> tac) -> tac
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

  let catch tac handle : tac =
    rule @@
    let* st = RM.get in 
    let* r = RM.trap @@ run tac in
    match r with
    | Ok (tm, tp) -> RM.ret (tm, tp)
    | Error exn ->
      let* () = RM.set st in
      run (handle exn)

  let whnf (name, tac) =
    rule ~name @@
    let* tm, tp = tac in
    RM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> RM.ret (tm, tp)
    | `Reduce tp' -> RM.ret (tm, tp')
end

module Tele =
struct
  type tac = string * S.tele RM.m

  let rule ?(name = "") tac = (name, tac)

  let run (name, tac) =
    debug_tactic name;
    tac

  let update_span loc (name, tac) =
    (name, RM.update_span loc tac)

  let whnf tac =
    tac
end

module KanTele =
struct
  type tac = string * (D.tp -> S.kan_tele RM.m)

  let rule ?(name = "") tac = (name, tac)

  let run (name, tac) tp =
    debug_tactic name;
    tac tp

  let update_span loc (name, tac) =
    (name, fun tp -> RM.update_span loc (tac tp))

  let whnf tac =
    tac
end

let abstract = Var.abstract

type var = Var.tac

let rec abstract_tele (tele : D.tele) (k : var list -> 'a RM.m) : 'a RM.m =
  match tele with
  | Cell (ident, tp, tele_clo) ->
    abstract ~ident tp @@ fun var ->
    let* tele = RM.lift_cmp @@ Sem.inst_tele_clo tele_clo (Var.con var) in
    abstract_tele tele (fun vars -> k (var :: vars))
  | Empty ->
    k []

let rec abstract_kan_tele (tele : D.kan_tele) (k : var list -> 'a RM.m) : 'a RM.m =
  match tele with
  | KCell (ident, code, tele_clo) ->
    let* tp = RM.lift_cmp @@ Sem.do_el code in
    abstract ~ident tp @@ fun var ->
    let* tele = RM.lift_cmp @@ Sem.inst_kan_tele_clo tele_clo (Var.con var) in
    abstract_kan_tele tele (fun vars -> k (var :: vars))
  | KEmpty ->
    k []
