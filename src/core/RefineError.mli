open Basis

include module type of RefineErrorData.Data
val pp : Format.formatter -> t -> unit

exception RefineError of t * LexingUtil.span option
