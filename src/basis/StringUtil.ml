let is_digit =
  function
  | '0' .. '9' -> true
  | _ -> false

let rpartition p s =
  let i = ref (String.length s-1) in
  while !i >= 0 && p (String.unsafe_get s !i) do decr i done;
  (CCString.take (!i+1) s, CCString.drop (!i+1) s)
