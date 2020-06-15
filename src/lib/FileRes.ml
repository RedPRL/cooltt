open Basis

(* todo: in a modular version of this, this would be a functor argument and the functions below would have more neutral names *)
let lib_name = "coollib"
let src_extention = ".cooltt"
let cache_extention = ".slush"

type filepath = string
type selector = string list (* todo/iev this is upath in my terminology *)

(* todo *)
(* let pp_selector =
 *   let pp_sep fmt () = Format.eprintf "." in
 *   Format.pp_print_list ~pp_sep Format.pp_print_string *)

let find_lib_root (base_dir : string) : string option =
  SysUtil.protect_cwd @@ fun _ -> (* todo used to be cur here *)
  let rec go cur =
    if Sys.file_exists lib_name then
      Some cur
    else
      let () = Sys.chdir Filename.parent_dir_name in
      let up = Sys.getcwd () in
      if up = cur then begin
        Log.pp_message ~loc:None ~lvl:`Warn
          Format.pp_print_string
          "You are using the special local import mode. This is not recommended. You have been warned.";
        None
      end else
        go up
  in
  Sys.chdir base_dir;
  go (Sys.getcwd ())

let selector_to_stem ~stem selector =
  let module_path = String.concat Filename.dir_sep selector in
  let base_dir = Filename.dirname stem in
  let base_dir = OptionUtil.default base_dir (find_lib_root base_dir) in
  Filename.concat base_dir module_path

let stem_to_cool stem = stem ^ src_extention

let stem_to_slush stem = stem ^ cache_extention

let cool_to_stem red =
  match String.sub red (String.length red - 4) 4 with
  | str when str = src_extention -> String.sub red 0 @@ String.length red - 4
  | _ -> invalid_arg "red_to_stem"
  | exception Invalid_argument _ -> invalid_arg "red_to_stem"
