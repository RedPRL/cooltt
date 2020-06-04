exception Not_found = Not_found

let protect_cwd f =
  let dir = Sys.getcwd () in
  match f dir with
  | ans -> Sys.chdir dir; ans
  | exception ext -> Sys.chdir dir; raise ext

let normalize ?(dirs=[]) path =
  protect_cwd @@ fun _ ->
  try
    List.iter Sys.chdir dirs;
    Sys.chdir (Filename.dirname path);
    Filename.concat (Sys.getcwd ()) (Filename.basename path)
  with Sys_error _ -> raise Not_found

let () : unit =
  if Filename.is_relative (Sys.getcwd ()) then
    failwith "Sys.getcwd returns a relative path."
  else
    ()
