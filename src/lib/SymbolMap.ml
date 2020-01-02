include Map.Make (Symbol)

let pp _ih fmt _table = 
  Format.fprintf fmt "<globals>"