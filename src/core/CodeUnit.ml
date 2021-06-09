module D = Domain

type fqn = { code_unit : string; index : int }

type t =
  { namespace : fqn Namespace.t;
    offset : int;
  }

let create offset = { namespace = Namespace.empty; offset = offset }

let add_global ident fqn cunit = { cunit with namespace = Namespace.add ident fqn cunit.namespace }

let resolve_global ident cunit = Namespace.find ident cunit.namespace
