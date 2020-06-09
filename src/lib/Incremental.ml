open CoolBasis

module Map = Map.Make (Name)

type params = int (* this is a place holder *)
type cx = int (* this is also a place holder *)

module M =
struct
  type 'a m = params -> cx -> cx * 'a

  let ret a _ cx = cx, a

  let bind m k ps cx =
    let cx', a = m ps cx in
    k a ps cx'

  let try_ m kerr ps cx =
    try
      m ps cx
    with exn ->
      kerr exn ps cx
end

module Notation = Monad.Notation (M)
include M
