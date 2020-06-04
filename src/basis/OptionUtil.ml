type 'a t = 'a option

let some x = Some x

let map f =
  function
  | Some a -> Some (f a)
  | None -> None

let foreach m f = map f m

let iter f =
  function
  | Some a -> f a
  | None -> ()

let rec filter_map f =
  function
  | [] -> []
  | (x :: xs) ->
    match f x with
    | Some y -> y :: filter_map f xs
    | None -> filter_map f xs

let filter_foreach l f = filter_map f l

let default a =
  function
  | None -> a
  | Some a -> a

exception WasNone

let get_exn m =
  match m with
  | Some x -> x
  | None ->
    Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
    Format.eprintf "@.";
    raise WasNone
