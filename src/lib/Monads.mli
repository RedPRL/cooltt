(** All the monads in this file keep track of a cofibration theory. *)

module D := Domain
module S := Syntax
module St := ElabState
open CoolBasis

type 'a compute
type 'a evaluate
type 'a split_quote
type 'a quote

(** The "computation" monad; contains enough state to run computations in the semantic domain,
    does not contain a variable environment or anything that would be needed for evaluation. *)
module CmpM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a compute

  val read_global : ElabState.t m
  val read_cof_env : CofEnv.env m

  val lift_ev : D.env -> 'a evaluate -> 'a m
  val test_sequent : D.cof list -> D.cof -> bool m

  val restore_cof_env : CofEnv.env -> 'a m -> 'a m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end

(** The "evaluation" monad; like the computation monad but keeps a variable environment. *)
module EvM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a evaluate

  val lift_cmp : 'a compute -> 'a m

  val read_global : ElabState.t m
  val read_local : D.env m

  val append : D.con list -> 'a m -> 'a m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end


(** The quotation environment keeps track of De Bruijn indices for use in conversion checking. *)
module SplitQuM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a split_quote

  val lift_cmp : 'a compute -> 'a m

  val restrict_ : D.cof list -> unit m -> unit m
  val bind_var_ : D.tp -> (D.con -> unit m) -> unit m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end

(** The quotation environment keeps track of De Bruijn indices for quotation. *)
module QuM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a quote

  val lift_cmp : 'a compute -> 'a m

  val read_global : ElabState.t m
  val read_local : int m
  val read_veil : Veil.t m

  val binder : int -> 'a m -> 'a m
  val bind_var : D.tp -> (D.con -> 'a m) -> 'a m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end

(** The elaboration monad is the "maximal" monad that can run code from any of the other monads. *)
module ElabM : sig
  include Monad.MonadReaderStateResult
    with type global := St.t
    with type local := ElabEnv.t

  val lift_qu : 'a quote -> 'a m
  val lift_sp_qu_ : unit split_quote -> unit m

  val lift_ev : 'a evaluate -> 'a m
  val lift_cmp : 'a compute -> 'a m

  val veil : Veil.t -> 'a m -> 'a m

  val globally : 'a m -> 'a m
  val emit : ?lvl:Log.level -> LexingUtil.span option -> (Format.formatter -> 'a -> unit) -> 'a -> unit m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end
