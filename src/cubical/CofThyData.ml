open Basis

type var = [`L of int | `G of Symbol.t]

type cof = (Dim.t, var) Cof.cof

let dump_var fmt : var -> unit =
  function
  | `L i -> Format.fprintf fmt "L[%i]" i
  | `G sym -> Format.fprintf fmt "G[%a]" Symbol.pp sym

let dump_cof = Cof.dump_cof Dim.dump dump_var
