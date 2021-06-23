open Bwd

module type S = sig
  type 'a m

  val ret : 'a -> 'a m

  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module type Notation = sig
  type 'a m

  val (let*) : 'a m -> ('a -> 'b m) -> 'b m
  val (and*) : 'a m -> 'b m -> ('a * 'b) m
  val (let+) : 'a m -> ('a -> 'b) -> 'b m
  val (and+) : 'a m -> 'b m -> ('a * 'b) m
  val (<@>) : ('a -> 'b) -> 'a m -> 'b m
  val (|>>) : 'a m -> ('a -> 'b m) -> 'b m
  val (@<<) : ('a -> 'b m) -> 'a m -> 'b m
  val (<&>) : 'a m -> 'b m -> ('a * 'b) m
end

module Notation (M : S) : Notation with type 'a m = 'a M.m = struct
  type 'a m = 'a M.m

  let (let*) = M.bind

  let (and*) m n =
    let* x = m in
    let* y = n in
    M.ret (x, y)

  let (let+) m f = M.bind m (fun x -> M.ret (f x))

  let (and+) m n = (and*) m n

  let (<@>) f m = (let+) m f
  let (|>>) = (let*)
  let (@<<) f m = m |>> f
  let (<&>) = (and+)
end

module Util (M : S) =
struct
  open Notation (M)

  let rec commute_list =
    function
    | [] -> M.ret []
    | m :: ms ->
      let+ x = m
      and+ xs = commute_list ms in
      x :: xs

  let rec map f =
    function
    | [] -> M.ret []
    | (x :: xs) ->
      let+ y = f x
      and+ ys = map f xs in
      y :: ys

  let rec filter_map f =
    function
    | [] -> M.ret []
    | (x :: xs) ->
      let+ oy = f x
      and+ ys = filter_map f xs in
      match oy with
      | None -> ys
      | Some y -> y :: ys

  let rec map_bwd f =
    function
    | Emp -> M.ret Emp
    | Snoc (xs, x) ->
      let+ xs = map_bwd f xs
      and+ x = f x in
      Snoc (xs, x)

  let rec iter f =
    function
    | [] -> M.ret ()
    | x :: xs -> let* () = f x in iter f xs

  let rec filter_map f =
    function
    | [] -> M.ret []
    | (x :: xs) ->
      let+ y = f x
      and+ ys = filter_map f xs in
      match y with
      | None -> ys
      | Some y -> y :: ys

  let ignore m =
    let+ _ = m in ()

  let rec fold_left_m f b =
    function
    | [] -> M.ret b
    | (x :: xs) -> M.bind (f x b) (fun b' -> fold_left_m f b' xs)

  let guard b action =
    if b then
      action ()
    else
      M.ret ()

  let first f (a, b) =
    let+ c = f a in
    (c, b)

  let second f (a, b) =
    let+ c = f b in
    (a, c)

  let map_accum_left_m f xs =
    let rec go acc =
      function
      | [] -> M.ret []
      | (x :: xs) ->
         let+ y = f acc x
         and+ ys = go (acc @ [x]) xs in
         y :: ys
    in
    go [] xs
end

module type MonadReaderResult = sig
  include S
  type local
  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val run : local -> 'a m -> ('a, exn) result
  val run_exn : local -> 'a m -> 'a
  val throw : exn -> 'a m
  val trap : 'a m -> ('a, exn) result m
end

module type MonadReaderStateResult = sig
  include S
  type global
  type local

  val read : local m
  val scope : (local -> local) -> 'a m -> 'a m
  val get : global m
  val set : global -> unit m
  val modify : (global -> global) -> unit m

  val run : global -> local -> 'a m -> ('a, exn) result
  val run_exn : global -> local -> 'a m -> 'a
  val run_globals_exn : global -> local -> 'a m -> ('a * global)
  val throw : exn -> 'a m
  val trap : 'a m -> ('a, exn) result m
end



module MonadReaderResult (X : sig type local end) =
struct
  type 'a m = X.local -> ('a, exn) result

  let ret a _ = Ok a

  let bind m k env =
    match m env with
    | Ok a -> k a env
    | Error exn -> Error exn

  let throw exn _ = Error exn

  let trap (m : 'a m) : ('a, exn) result m =
    fun env ->
    Ok (m env)

  let read env = Ok env
  let scope f m env = m @@ f env

  let run env m = m env

  let run_exn env m =
    match run env m with
    | Ok a -> a
    | Error exn -> raise exn

end

module MonadReaderStateResult (X : sig type global type local end) =
struct
  type 'a m = X.global * X.local -> ('a, exn) result * X.global

  let ret a (st, _) = Ok a, st

  let bind m k (st, env) =
    match m (st, env) with
    | Ok a, st' -> k a (st', env)
    | Error exn, st' -> Error exn, st'

  let throw exn (st, _) = Error exn, st


  let trap (m : 'a m) : ('a, exn) result m =
    fun env ->
    match m env with
    | Ok a, st -> Ok (Ok a), st
    | Error exn, st -> Ok (Error exn), st

  let read (st, env) = Ok env, st

  let scope f m (st, env) = m (st, f env)
  let get (st, _) = Ok st, st
  let set st (_, _) = Ok (), st

  let modify f (st, _) = Ok (), f st

  let run st env m =
    let a, _ = m (st, env) in
    a

  let run_exn st env m =
    match run st env m with
    | Ok a -> a
    | Error exn -> raise exn

  let run_globals_exn st env m =
    match m (st, env) with
    | (Ok a, st') -> (a, st')
    | (Error exn, _) -> raise exn
end
