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

let rec map_opt f = function
  | [] -> Some []
  | (x :: xs) ->
     match f x with
     | Some y -> Option.map (fun ys -> y :: ys) (map_opt f xs)
     | None -> None
