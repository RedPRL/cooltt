open Basis
open CodeUnit

module D = Domain
module S = Syntax

include RefineErrorData.Data

module Fmt = Format

let pp_connective fmt =
  function
  | `Cof ->
    Format.fprintf fmt "cof"
  | `Dim ->
    Format.fprintf fmt "dim"
  | `DDim ->
    Format.fprintf fmt "ddim"
  | `Pi ->
    Format.fprintf fmt "pi"
  | `Sg ->
    Format.fprintf fmt "sg"
  | `Signature ->
    Format.fprintf fmt "sig"
  | `Univ ->
    Format.fprintf fmt "univ"
  | `Nat ->
    Format.fprintf fmt "nat"
  | `Circle ->
    Format.fprintf fmt "circle"
  | `Sub ->
    Format.fprintf fmt "sub"
  | `Prf ->
    Format.fprintf fmt "prf"
  | `El ->
    Format.fprintf fmt "el"
  | `ElV ->
    Format.fprintf fmt "V"
  | `ElHCom ->
    Format.fprintf fmt "hcom"
  | `ElExt ->
    Format.fprintf fmt "ext"
  | `ElCFill ->
    Format.fprintf fmt "cfill"
  | `DomTp ->
    Format.fprintf fmt "dom"
  | `ElSub ->
    Format.fprintf fmt "sub'"

let pp fmt =
  function
  | UnboundVariable id ->
    Fmt.fprintf fmt "Unbound variable %a" Ident.pp id
  | ExpectedEqual (ppenv, tp, tm0, tm1, _) ->
    Fmt.fprintf fmt
      "Expected equal terms @[<hv>%a =@;%a@;: %a@]"
      (S.pp ppenv) tm0
      (S.pp ppenv) tm1
      (S.pp_tp ppenv) tp
  | ExpectedEqualTypes (ppenv, tp0, tp1, _) ->
    Fmt.fprintf fmt
      "Expected equal types @[<hv>%a =@;%a@]"
      (S.pp_tp ppenv) tp0
      (S.pp_tp ppenv) tp1
  | ExpectedConnective (conn, ppenv, tp) ->
    Fmt.fprintf fmt
      "Head connective mismatch, expected %a but got %a"
      pp_connective conn
      (S.pp_tp ppenv) tp
  | ExpectedOnOf (ppenv, tps) ->
    Fmt.fprintf fmt
      "Expected a term of one of %a" (Format.pp_print_list (S.pp_tp ppenv)) tps
  | ExpectedDimensionLiteral n ->
    Fmt.fprintf fmt
      "Expected dimension literal 0 or 1, but got %i" n
  | ExpectedDDimensionLiteral n ->
    Fmt.fprintf fmt
      "Expected directed dimension literal 0 or 1, but got %i" n
  | ExpectedOfMatchingIntervalType (ppenv, tm0 , tm1) ->
    Fmt.fprintf fmt "Expected %a and %a to be terms of a matching interval type"
      (S.pp ppenv) tm0
      (S.pp ppenv) tm1
  | ExpectedTrue (ppenv, cof) ->
    Fmt.fprintf fmt
      "Expected true cofibration: %a"
      (S.pp ppenv) cof
  | ExpectedField (ppenv, sign, tm, lbl) ->
    Fmt.fprintf fmt "Expected (%a : sig %a) to have field %a" (S.pp ppenv) tm (S.pp_sign ppenv) sign Ident.pp_user lbl
  | FieldNameMismatches (expected, actual) ->
    Fmt.fprintf fmt "Field names mismatch, expected [%a] but got [%a]" (Pp.pp_sep_list Ident.pp_user) expected (Pp.pp_sep_list Ident.pp_user) actual
  | VirtualType ->
    Fmt.fprintf fmt "Virtual type (dim, cof, etc.) cannot appear in this position"
  | HoleNotPermitted (ppenv, tp) ->
    Fmt.fprintf fmt
      "Holes of type %a are not permitted"
      (S.pp_tp ppenv) tp
  | BindingNotFound (`User []) ->
    Fmt.fprintf fmt
      "No bindings"
  | BindingNotFound id ->
    Fmt.fprintf fmt
      "No bindings with the prefix %a" Ident.pp_user id
  | UnexpectedShadowing id ->
    Fmt.fprintf fmt
      "Unexpected shadowing of %a" Ident.pp_user id
  | CyclicImport id ->
    Fmt.fprintf fmt
      "Cyclic import of %a" CodeUnitID.pp id
  | RefineErrorData.Data.ErrorsInSection -> (* qualified names to check spellings *)
    Fmt.fprintf fmt
      "Unexpected errors in sections"
  | UnsolvedHoles 1 ->
    Fmt.fprintf fmt
      "There is 1 unsolved hole"
  | UnsolvedHoles n ->
    Fmt.fprintf fmt
      "There are %i unsolved holes" n
  | ExpectedSignature (ppenv, tm) ->
    Fmt.fprintf fmt
      "Expected signature but got %a" (S.pp ppenv) tm
  | ExpectedStructure (ppenv, tm) ->
    Fmt.fprintf fmt
      "Expected structure but got %a" (S.pp ppenv) tm
  | ExpectedDomVar (ppenv, ix) -> 
    Fmt.fprintf fmt "Variable %s is not a domain variable!" (Pp.Env.var ix ppenv)




exception RefineError of t * LexingUtil.span option

let _ =
  PpExn.install_printer @@ fun fmt ->
  function
  | RefineError (err, _loc) ->
    pp fmt err
  | _ ->
    raise PpExn.Unrecognized
