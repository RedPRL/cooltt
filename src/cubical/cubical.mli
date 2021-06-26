(** The {!module:Cubical} library implements the syntax and semantics of the Cartesian interval as well as a logic of cofibrations as described by {{:https://github.com/dlicata335/cart-cube/blob/master/cart-cube.pdf} ABCFHL}. *)

(** {1 Syntax} *)

(** The abstract syntax of the Cartesian interval. *)
module Dim : module type of Dim

(** The abstract syntax of the restricted predicate logic of cofibrations. *)
module Cof : module type of Cof

module DimProbe : module type of DimProbe

(** The {!module:CofThy} module implements decision procedures for sequents relative to a theory over the interval, stated in the language of cofibrations. *)
module CofThy : module type of CofThy
