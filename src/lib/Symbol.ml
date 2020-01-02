type t = {gen : int; name : string option}
[@@deriving show]

let global = ref 0

let compare s1 s2 = 
  Int.compare s1.gen s2.gen

let equal s1 s2 = 
  s1.gen = s2.gen

let fresh () = 
  let i = !global in
  let s = {gen = i; name = None} in
  global := i + 1;
  s

let named str = 
  let i = !global in
  let s = {gen = i; name = Some str} in
  global := i + 1;
  s