type 'a bwd =
  | Emp
  | Snoc of 'a bwd * 'a

[@@deriving show]

module BwdNotation =
struct
  let (#<) xs x =
    Snoc (xs, x)

  let rec (<.>) xs ys =
    match ys with
    | Emp -> xs
    | Snoc (ys, y) ->
      Snoc (xs <.> ys, y)


  let rec (<><) xs ys =
    match ys with
    | [] -> xs
    | y :: ys -> (xs #< y) <>< ys

  let rec (<>>) xs ys =
    match xs with
    | Emp -> ys
    | Snoc (xs, x) -> xs <>> x :: ys
end

module Bwd =
struct
  open BwdNotation

  let rec nth xs i =
    match xs with
    | Emp ->
      failwith "Bwd.nth"
    | Snoc (_, x) when i = 0 -> x
    | Snoc (xs, _) -> nth xs @@ i - 1

  let rec mem a xs =
    match xs with
    | Emp -> false
    | Snoc (xs, x) ->
      a = x || (mem[@tailcall]) a xs

  let rec exists p xs =
    match xs with
    | Emp -> false
    | Snoc (xs, x) ->
      p x || (exists[@tailcall]) p xs

  let rec for_all p xs =
    match xs with
    | Emp -> true
    | Snoc (xs, x) ->
      p x && (for_all[@tailcall]) p xs

  let rec iter p xs =
    match xs with
    | Emp -> ()
    | Snoc (xs, x) ->
      p x; (iter[@tailcall]) p xs

  let rec length =
    function
    | Emp -> 0
    | Snoc (xs, _) ->
      1 + length xs

  let rec map f =
    function
    | Emp -> Emp
    | Snoc (xs, x) -> Snoc (map f xs, f x)

  let rec filter_map f =
    function
    | Emp -> Emp
    | Snoc (xs, x) ->
      match f x with 
      | None -> filter_map f xs
      | Some fx -> Snoc (filter_map f xs, fx)

  let mapi f =
    let rec go i =
      function
      | Emp -> Emp
      | Snoc (xs, x) -> Snoc (go (i + 1) xs, f i x)
    in
    go 0

  let rec flat_map f =
    function
    | Emp -> Emp
    | Snoc (xs, x) -> flat_map f xs <>< f x

  let rec filter f =
    function
    | Emp -> Emp
    | Snoc (xs, x) ->
      let xs' = filter f xs in
      if f x then Snoc (xs', x) else xs'

  let rec fold_left f e =
    function
    | Emp -> e
    | Snoc (xs, x) ->
      f (fold_left f e xs) x

  let rec fold_right f l e =
    match l with
    | Emp -> e
    | Snoc (l, x) ->
      let e = f x e in
      (fold_right[@tailcall]) f l e

  let rec fold_right2 f l0 l1 e =
    match l0, l1 with
    | Emp, Emp -> e
    | Snoc (l0, x0), Snoc (l1, x1) ->
      let e = f x0 x1 e in
      (fold_right2[@tailcall]) f l0 l1 e
    | _ -> raise @@ Invalid_argument "Bwd.fold_right2"
  let to_list xs =
    xs <>> []

  let from_list xs =
    Emp <>< xs

  (* favonia: the following is considered ILL-TYPED!
   *
   * let rev xs = from_list @@ List.rev @@ to_list xs *)
end