open TLNat

type (_, _) vec =
  | [] : (ze, 'a) vec
  | (::) : 'a * ('n, 'a) vec -> ('n su, 'a) vec

let rec to_list : type n. (n, 'a) vec -> 'a list =
  function 
  | [] -> []
  | x :: xs -> x :: to_list xs