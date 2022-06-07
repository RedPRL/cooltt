type 'a printer = Format.formatter -> 'a -> unit

module Env :
sig
  type t
  val emp : t
  val var : int -> t -> string
  val bind : t -> string option -> string * t
  val bindn : t -> string option list -> string list * t
  val bind_underscore : t -> string * t

  val proj : t -> t
  val names : t -> string list
end

val pp_sep_list : ?sep:string -> 'a printer -> ('a list) printer

type env = Env.t
