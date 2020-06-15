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

  val make : S.tp EM.m -> tac
  val make_virtual : S.tp EM.m -> tac

  val run : tac -> S.tp EM.m
  val run_virtual : tac -> S.tp EM.m
  val map : (S.tp EM.m -> S.tp EM.m) -> tac -> tac
end
=
struct
  type tac =
    | Virtual of S.tp EM.m
    | General of S.tp EM.m

  let make tac = General tac
  let make_virtual tac = Virtual tac

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

module Var =
struct
  type tac = {tp : D.tp; con : D.con}

  let prf phi = {tp = D.TpPrf phi; con = D.Prf}
  let con {tp = _; con} = con
  let syn {tp; con} =
    let+ tm = EM.quote_con tp con in
    tm, tp
end

let abstract : ?ident:Ident.t -> D.tp -> (Var.tac -> 'a EM.m) -> 'a EM.m =
  fun ?(ident = `Anon) tp kont ->
  EM.abstract ident tp @@ fun (con : D.con) ->
  kont @@ {tp; con}


module rec Chk : sig
  include Tactic with type tac = D.tp -> S.t EM.m

  val make : (D.tp -> S.t EM.m) -> tac
  val run : tac -> D.tp -> S.t EM.m

  val bchk : BChk.tac -> tac
  val syn : Syn.tac -> tac
end =
struct
  type tac = D.tp -> S.t EM.m

  let run tac = tac
  let make tac = tac

  let update_span loc tac tp =
    EM.update_span loc @@ tac tp

  let bchk : BChk.tac -> tac =
    fun btac tp ->
    let triv = D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp}) in
    btac (tp, Cof.bot, triv)

  let syn (tac : Syn.tac) : tac =
    fun tp ->
    let* tm, tp' = tac in
    let+ () = EM.equate_tp tp tp' in
    tm

  let whnf tac =
    fun tp ->
    EM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> tac tp
    | `Reduce tp -> tac tp
end

and BChk : sig
  include Tactic with type tac = D.tp * D.cof * D.tm_clo -> S.t EM.m

  val make : (D.tp * D.cof * D.tm_clo -> S.t EM.m) -> tac
  val run : tac -> D.tp * D.cof * D.tm_clo -> S.t EM.m

  val chk : Chk.tac -> tac
  val syn : Syn.tac -> tac
end =
struct
  type tac = D.tp * D.cof * D.tm_clo -> S.t EM.m

  let run tac = tac
  let make tac = tac

  let update_span loc tac goal =
    EM.update_span loc @@ tac goal

  let chk : Chk.tac -> tac =
    fun tac (tp, phi, pclo) ->
    let* tm = tac tp in
    let* con = EM.lift_ev @@ Sem.eval tm in
    let* () =
      abstract (D.TpPrf phi) @@ fun prf ->
      EM.equate tp con @<< EM.lift_cmp @@ Sem.inst_tm_clo pclo @@ Var.con prf
    in
    EM.ret tm

  let syn : Syn.tac -> tac =
    fun tac ->
    chk @@ Chk.syn tac

  let whnf tac =
    fun (tp, phi, clo) ->
    EM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> tac (tp, phi, clo)
    | `Reduce tp -> tac (tp, phi, clo)
end

and Syn : sig
  include Tactic with type tac = (S.t * D.tp) EM.m
  val make : (S.t * D.tp) EM.m -> tac
  val run : tac -> (S.t * D.tp) EM.m
  val ann : Chk.tac -> Tp.tac -> tac
end =
struct
  type tac = (S.t * D.tp) EM.m

  let make tac = tac
  let run tac = tac

  let update_span loc =
    EM.update_span loc

  let ann (tac_tm : Chk.tac) (tac_tp : Tp.tac) : tac =
    let* tp = Tp.run tac_tp in
    let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
    let+ tm = tac_tm vtp in
    tm, vtp

  let whnf tac =
    let* tm, tp = tac in
    EM.lift_cmp @@ Sem.whnf_tp tp |>>
    function
    | `Done -> EM.ret (tm, tp)
    | `Reduce tp' -> EM.ret (tm, tp')
end


type var = Var.tac
type tp_tac = Tp.tac
