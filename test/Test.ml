open Frontend

let header fname =
  String.make 20 '-' ^ "[" ^ fname ^ "]" ^ String.make 20 '-' ^ "\n"

let execute_file fname =
  if String.equal (Filename.extension fname) ".cooltt" then
    let _ = print_string (header fname) in
    ignore @@ Driver.load_file ~as_file:None ~debug_mode:false (`File fname)

let () =
  let cooltt_files = Sys.readdir "." in
  Array.sort String.compare cooltt_files;
  Array.iter execute_file cooltt_files
