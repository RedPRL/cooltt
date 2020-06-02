let rec take n =
  if n > 0 then
    function
    | [] -> []
    | x :: xs -> x :: take (n - 1) xs
  else
    fun _ -> []
