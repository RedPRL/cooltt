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
