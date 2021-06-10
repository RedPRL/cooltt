open Frontend

let () =
  List.iter (fun fname -> ignore @@ Driver.process_file (`File fname))
  @@ List.sort String.compare
  @@ List.filter (fun fname -> String.equal (Filename.extension fname) ".cooltt")
  @@ Array.to_list
  @@ Sys.readdir "."
