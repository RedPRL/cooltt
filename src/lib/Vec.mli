open TLNat

type (_, _) vec =
  | [] : (ze, 'a) vec
  | (::) : 'a * ('n, 'a) vec -> ('n su, 'a) vec

val to_list : ('n, 'a) vec -> 'a list