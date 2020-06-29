(** All the monads in this file keep track of a cofibration theory. *)

module D := Domain
module S := Syntax
module St := ElabState

open Basis
open Cubical

type 'a compute
type 'a evaluate
type 'a conversion
type 'a quote

(** The "computation" monad; contains enough state to run computations in the semantic domain,
    does not contain a variable environment or anything that would be needed for evaluation. *)
module CmpM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a compute

  val read_global : ElabState.t m
  val read_cof_thy : CofThy.Disj.t m

  val lift_ev : D.env -> 'a evaluate -> 'a m
  val test_sequent : D.cof list -> D.cof -> bool m

  val restore_cof_thy : CofThy.Disj.t -> 'a m -> 'a m

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
  val drop_con : 'a m -> 'a m
  val drop_all_cons : 'a m -> 'a m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end


(** The conversion environment keeps track of De Bruijn indices for use in conversion checking. *)
module ConvM : sig
  include Monad.MonadReaderResult
    with type 'a m = 'a conversion

  val lift_cmp : 'a compute -> 'a m

  val restrict_ : D.cof list -> unit m -> unit m
  val bind_var_ : D.tp -> (D.con -> unit m) -> unit m

  val globally : 'a m -> 'a m

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

  val globally : 'a m -> 'a m

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
  val lift_conv_ : unit conversion -> unit m

  val lift_ev : 'a evaluate -> 'a m
  val lift_cmp : 'a compute -> 'a m

  val veil : Veil.t -> 'a m -> 'a m

  val globally : 'a m -> 'a m
  val emit : ?lvl:Log.level -> ?last_token:string -> LexingUtil.span option -> (Format.formatter -> 'a -> unit) -> 'a -> unit m

  val abort_if_inconsistent : 'a m -> 'a m -> 'a m
end
