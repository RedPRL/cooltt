open Frontend

let execute_file fname =
  if String.equal (Filename.extension fname) ".cooltt" then
    let _ = print_string @@ "Processing " ^ fname ^ "\n" in
    ignore @@ Driver.process_file (`File fname)

let () =
  let cooltt_files = Sys.readdir "." in
  Array.sort String.compare cooltt_files;
  Array.iter execute_file cooltt_files
