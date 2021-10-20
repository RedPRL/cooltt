open Bwd

let rec zip xs ys =
  match xs, ys with
  | (x :: xs, y :: ys) -> (x, y) :: zip xs ys
  | _, _ -> []

let rec unzip =
  function
  | [] -> ([], [])
  | ((x, y) :: xs) ->
    let (xs, ys) = unzip xs in
    (x :: xs, y :: ys)

let zip_with f xs ys =
  let rec go acc xs ys =
    match xs, ys with
    | x :: xs, y :: ys -> go (Snoc (acc, f x y)) xs ys
    | _, _ -> Bwd.to_list acc
  in go Emp xs ys


let rec map_opt f = function
  | [] -> Some []
  | (x :: xs) ->
    match f x with
    | Some y -> Option.map (fun ys -> y :: ys) (map_opt f xs)
    | None -> None

let map_accum_left (f : 'a -> 'b -> 'a * 'c) (e : 'a) (xs : ' b list) : 'a * 'c list =
  let rec go e ys =
    function
    | [] -> (e, Bwd.to_list ys)
    | (x :: xs) ->
      let (e, y) = f e x in
      (go[@tailcall]) e (Snoc (ys, y)) xs
  in go e Emp xs
