open Basis

type var = int

type cof = (Dim.t, var) Cof.cof

let dump_var fmt i = Format.fprintf fmt "L[%i]" i

let dump_cof = Cof.dump_cof Dim.dump dump_var
