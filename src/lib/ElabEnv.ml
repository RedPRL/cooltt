type t = {check_env : Check.env; bindings : string list}

let init = {check_env = Check.Env.empty; bindings = []}

let bindings {bindings; _} = bindings

let check_env {check_env; _} = check_env

let push_name i env = {env with bindings = i :: env.bindings}

let push_names is env = {env with bindings = is @ env.bindings}

let find_ix key env =
  let exception E in
  let rec go i = function
    | [] -> raise E
    | x :: xs -> if String.equal x key then i else go (i + 1) xs
  in
  match go 0 @@ bindings env with
  | i -> Some i
  | exception E -> None

let add_top_level ~term ~tp env =
  {env with check_env = Check.Env.add_top_level ~term ~tp env.check_env}

let add_term ~term ~tp env =
  {env with check_env = Check.Env.add_term ~term ~tp env.check_env}