exception Unrecognized

let printers = Stack.create ()

let install_printer printer =
  Stack.push printer printers;
  Printexc.register_printer @@ fun exn ->
  try
    printer Format.str_formatter exn;
    Some (Format.flush_str_formatter ())
  with
  | Unrecognized ->
    None

let pp fmt exn =
  let exception Break in
  let go printer =
    try
      printer fmt exn;
      raise Break
    with
    | Unrecognized -> ()
  in
  try
    Stack.iter go printers;
    Format.fprintf fmt "%s" @@ Printexc.to_string exn
  with
  | Break -> ()