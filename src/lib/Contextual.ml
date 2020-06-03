open Dev
open RedTT_Core
open RedBasis
open Bwd open BwdNotation


module Map = Map.Make (Name)

type rotted_resolver = ResEnv.t * Digest.t

(** this is the environment that will stay there for the entire thread *)
type thread_env =
  {env : GlobalEnv.t; (** the mapping from names to associated definitions (if any). *)
   rigidity : [`Flex | `Rigid] Map.t; (** whether a particular name is rigid. *)
   source : FileRes.filepath Map.t; (** the mapping from the name to the file path *)
   resolver_cache : (FileRes.filepath, [`Checked of rotted_resolver | `Checking]) Hashtbl.t (** the cache of all resolvers from fully elaborated modules *)
  }

(** this is the environment that only makes sense in a particular module. *)
type module_env =
  {mlenv : ML.mlenv; (** the environment for *)
   resenv : ResEnv.t (** the map from strings to names within a particular *)
  }

(** the local environmeth that only makes sense in a particular region of a module. *)
type local_env =
  {lcx : entry bwd;
   rcx : [`Entry of entry | `Update of Occurs.Set.t] list
  }

type cx = {
  th : thread_env;
  mo : module_env;
  lo : local_env
}

let rec pp_lcx fmt =
  function
  | Emp ->
    ()
  | Snoc (Emp, e) ->
    Format.fprintf fmt "@[<v>%a@]"
      pp_entry e
  | Snoc (cx, e) ->
    Format.fprintf fmt "%a;@;@;@[<v>%a@]"
      pp_lcx cx
      pp_entry e

let rec pp_rcx fmt =
  function
  | [] ->
    ()
  | e :: [] ->
    Format.fprintf fmt "@[<1>%a@]"
      pp_entry e
  | e :: cx ->
    Format.fprintf fmt "@[<1>%a@];@;@;%a"
      pp_entry e
      pp_rcx cx

let rec rcx_entries es =
  match es with
  | [] -> []
  | `Entry e :: es -> e :: rcx_entries es
  | _ :: es -> rcx_entries es


let filter_entry filter entry =
  match filter with
  | `All -> true
  | `Constraints ->
    begin
      match entry with
      | Q _ -> true
      | _ -> false
    end
  | `Unsolved ->
    begin
      match entry with
      | Q _ -> true
      | E (_, _, Hole _) -> true
      | E (_, _, Guess _) -> true
      | _ -> false
    end

let pp_cx filter fmt {lo = {lcx; rcx}; _} =
  Format.fprintf fmt "@[<v>%a@]@ %a@ @[<v>%a@]"
    pp_lcx (Bwd.filter (filter_entry filter) lcx)
    Uuseg_string.pp_utf_8 "❚"
    pp_rcx (List.filter (filter_entry filter) @@ rcx_entries rcx)


module M =
struct
  type 'a m = params -> cx -> cx * 'a

  let ret a _ cx = cx, a

  let bind m k ps cx =
    let cx', a = m ps cx in
    k a ps cx'

  let try_ m kerr ps cx =
    try
      m ps cx
    with exn ->
      kerr exn ps cx
end

module Notation = Monad.Notation (M)
include M

open Notation


let rec fix f ps cx =
  f (fix f) ps cx

let local f m ps =
  m (f ps)

let optional m ps cx =
  try
    let cx', a = m ps cx in
    cx', Some a
  with
  | _ -> cx, None

let ask ps cx = cx, ps

let get _ cx = cx, cx

let modify f _ cx = f cx, ()

let getth = get <<@> fun x -> x.th
let getlo = get <<@> fun x -> x.lo
let getmo = get <<@> fun x -> x.mo

let modifyth f = modify @@ fun st -> {st with th = f st.th}
let modifymo f = modify @@ fun st -> {st with mo = f st.mo}
let modifylo f = modify @@ fun st -> {st with lo = f st.lo}

let getl = getlo <<@> fun x -> x.lcx
let getr = getlo <<@> fun x -> x.rcx
let modifyl f = modifylo @@ fun st -> {st with lcx = f st.lcx}
let modifyr f = modifylo @@ fun st -> {st with rcx = f st.rcx}
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r

let modify_mlenv f =
  modifymo @@ fun st ->
  {st with mlenv = f st.mlenv}

let mlenv = getmo <<@> fun st -> st.mlenv

let mlconf = mlenv <<@> ML.Env.mlconf


let assert_top_level =
  ask >>= function
  | Emp -> ret ()
  | _ -> failwith "Invalid operations outside of the top-level."

let update_env e =
  match e with
  | E (nm, ty, Hole rigidity) ->
    modifyth @@ fun th ->
    {th with
     env = GlobalEnv.ext_meta th.env nm ty;
     rigidity = Map.add nm rigidity th.rigidity}
  | E (nm, ty, Guess _) ->
    modifyth @@ fun th ->
    {th with
     env = GlobalEnv.ext_meta th.env nm ty;
     rigidity = Map.add nm `Rigid th.rigidity}
  | E (nm, ty, Auxiliary tm) ->
    modifyth @@ fun th ->
    {th with
     env = GlobalEnv.define th.env nm ty tm;
     rigidity = Map.add nm `Rigid th.rigidity}
  | E (nm, ty, UserDefn {source; visibility; opacity; tm}) ->
    modifyth begin fun th ->
      {th with
       env =
         begin
           match opacity with
           | `Transparent -> GlobalEnv.define th.env nm ty tm
           | `Opaque -> GlobalEnv.ext_meta th.env nm ty
         end;
       rigidity = Map.add nm `Rigid th.rigidity;
       source = Map.add nm source th.source}
    end >>
    modifymo @@ fun mo ->
    {mo with resenv = ResEnv.add_native_global ~visibility nm mo.resenv}
  | Q _ -> ret ()

let declare_datatype ~src visibility dlbl desc =
  modify @@ fun st ->
  {st with
   th =
     {st.th with
      env = GlobalEnv.declare_datatype dlbl desc st.th.env;
      source = Map.add dlbl src st.th.source};
   mo = {st.mo with resenv = ResEnv.add_native_global visibility dlbl st.mo.resenv}}

let replace_datatype dlbl desc =
  modifyth @@ fun th ->
  {th with env = GlobalEnv.replace_datatype dlbl desc th.env}

let source_stem name =
  getth <<@> fun {source; _} -> Map.find_opt name source

exception CyclicDependency

let retrieve_module ~stem =
  getth <<@> fun {resolver_cache; _} ->
  match Hashtbl.find_opt resolver_cache stem with
  | Some (`Checked res) -> Some res
  | Some `Checking -> raise CyclicDependency
  | None -> None

let store_module ~stem res =
  getth <<@> fun {resolver_cache; _} -> Hashtbl.replace resolver_cache stem (`Checked res)

let touch_module ~stem =
  getth <<@> fun {resolver_cache; _} -> Hashtbl.replace resolver_cache stem `Checking




let pushl e =
  modifyl (fun es -> es #< e) >>
  update_env e

let pushr e =
  modifyr (fun es -> `Entry e :: es) >>
  update_env e

let init_th () =
  {env = GlobalEnv.emp (); rigidity = Map.empty; source = Map.empty; resolver_cache = Hashtbl.create 100}
let init_mo ~mlconf =
  {resenv = ResEnv.init (); mlenv = ML.Env.init ~mlconf}
let init_lo () =
  {lcx = Emp; rcx = []}

let run ~mlconf (m : 'a m) : 'a  =
  let th = init_th () in
  let mo = init_mo ~mlconf in
  let lo = init_lo () in
  let _, r = m Emp {th; mo; lo} in
  r

let isolate_local (m : 'a m) : 'a m =
  fun ps st ->
    let st', a = m ps {st with lo = init_lo ()} in
    {st' with lo = {lcx = st.lo.lcx <.> st'.lo.lcx; rcx = st'.lo.rcx @ st.lo.rcx}}, a

let isolate_module ~mlconf (m : 'a m) : 'a m =
  assert_top_level >>
  fun ps st ->
  let st', a = m ps {st with mo = init_mo ~mlconf; lo = init_lo ()} in
  {st' with mo = st.mo; lo = st.lo}, a

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let dump_state fmt str filter =
  get >>= fun cx ->
  Format.fprintf fmt "@[<v2>%s@,@,@[<v>%a@]@]@.@." str (pp_cx filter) cx;
  ret ()

let popl =
  getl >>= function
  | Snoc (mcx, e) -> setl mcx >> ret e
  | _ ->
    dump_state Format.err_formatter "Tried to pop-left" `All >>= fun _ ->
    failwith "popl: empty"

let global_env =
  get >>= fun st ->
  let rec go_params =
    function
    | Emp -> st.th.env
    | Snoc (psi, (x, (`I | `P _ | `Def _ | `Tw _ as entry))) ->
      GlobalEnv.ext (go_params psi) x entry
    | Snoc (psi, (_, `R (r0, r1))) ->
      GlobalEnv.restrict r0 r1 (go_params psi)
    | Snoc (psi, (_, `NullaryExt)) ->
      go_params psi
  in
  ask >>= fun psi ->
  ret @@ go_params psi

let lookup_top_ x =
  getth >>= fun th ->
  let entry = GlobalEnv.lookup th.env x in
  let rigidity = Map.find_opt x th.rigidity in
  ret (entry, rigidity)

let lookup_top x =
  assert_top_level >>
  lookup_top_ x

let restore_top x ~stem (entry, rigidity) =
  assert_top_level >>
  modifyth @@ fun th ->
  {th with
   env = GlobalEnv.ext th.env x entry;
   rigidity = Map.update x (fun _ -> rigidity) th.rigidity;
   source = Map.add x stem th.source}

let resolver =
  let rec go_locals renv =
    function
    | Emp -> renv
    | Snoc (psi, (x, _)) ->
      let renv = go_locals renv psi in
      ResEnv.add_native_global `Private x renv
  in

  get >>= fun st ->
  ask >>= fun psi ->
  M.ret @@ go_locals st.mo.resenv psi

let modify_top_resolver f =
  assert_top_level >>
  modifymo @@ fun mo ->
  {mo with resenv = f mo.resenv}

let popr_opt =
  let rec go theta =
    getr >>= function
    | `Entry e :: rcx ->
      setr (`Update theta :: rcx) >>
      if Occurs.Set.is_empty theta then
        ret @@ Some e
      else
        get >>= fun st ->
        ret @@ Some (Entry.subst st.th.env e)
    | `Update theta' :: rcx ->
      setr rcx >>
      go @@ Occurs.Set.union theta theta'
    | [] ->
      ret None
  in
  go Occurs.Set.empty

let push_update x =
  modifyr @@ fun rcx ->
  `Update (Occurs.Set.singleton x) :: rcx

let popr =
  popr_opt >>= function
  | Some e -> ret e
  | None -> failwith "popr: empty"

let go_left =
  popl >>= pushr


let go_to_top =
  getlo >>= fun {lcx; rcx} ->
  setl Emp >>
  setr (Bwd.map (fun e -> `Entry e) lcx <>> rcx)

let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)

let in_scopes ps =
  local @@ fun ps' ->
  ps' <>< ps


let lookup_meta x =
  getth >>= fun th ->
  let ty = GlobalEnv.lookup_ty th.env x `Only in
  let rigidity = Map.find x th.rigidity in
  ret (ty, rigidity)

let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, `P ty)) ->
      if x = y then M.ret ty else go gm
    | `Only, Snoc (gm, (y, `Def (ty, _))) ->
      if x = y then M.ret ty else go gm
    | `TwinL, Snoc (gm, (y, `Tw (ty0, _))) ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, Snoc (gm, (y, `Tw (_, ty1))) ->
      if x = y then M.ret ty1 else go gm
    | _, Snoc (gm, _) ->
      go gm
    | _, Emp ->
      getth >>= fun th ->
      ret @@ GlobalEnv.lookup_ty th.env x w
  in
  ask >>= go


let postpone s p =
  ask >>= fun ps ->
  let wrapped =
    let rec go ps p =
      match ps with
      | Emp ->
        p
      | Snoc (ps, (x, param)) ->
        go ps @@ All (param, Dev.bind x param p)
    in go ps p
  in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked


let base_cx =
  global_env >>= fun env ->
  ret @@ Cx.init env


let check ~ty ?sys:(sys = []) tm =
  base_cx >>= fun lcx ->
  let vty = Cx.eval lcx ty in
  let vsys = Cx.eval_tm_sys lcx sys in
  try
    Typing.check_ lcx vty vsys tm;
    ret `Ok
  with
  | exn ->
    ret @@ `Exn (exn, Printexc.get_raw_backtrace ())

let check_eq ~ty tm0 tm1 =
  if tm0 = tm1 then ret `Ok else
    base_cx >>= fun lcx ->
    let vty = Cx.eval lcx ty in
    let el0 = Cx.eval lcx tm0 in
    let el1 = Cx.eval lcx tm1 in
    try
      Cx.check_eq lcx ~ty:vty el0 el1;
      ret `Ok
    with
    | exn ->
      ret @@ `Exn (exn, Printexc.get_raw_backtrace ())

let check_subtype ty0 ty1 =
  base_cx >>= fun lcx ->
  let vty0 = Cx.eval lcx ty0 in
  let vty1 = Cx.eval lcx ty1 in
  try
    Cx.check_subtype lcx vty0 vty1;
    ret `Ok
  with
  | exn ->
    ret @@ `Exn (exn, Printexc.get_raw_backtrace ())

let compare_dim tr0 tr1 =
  base_cx >>= fun cx ->
  let r0 = Cx.eval_dim cx tr0 in
  let r1 = Cx.eval_dim cx tr1 in
  ret @@ I.compare r0 r1

let check_eq_dim tr0 tr1 =
  base_cx >>= fun cx ->
  let r0 = Cx.eval_dim cx tr0 in
  let r1 = Cx.eval_dim cx tr1 in
  match I.compare r0 r1 with
  | `Same ->
    ret true
  | _ ->
    ret false

let under_restriction r0 r1 m =
  compare_dim r0 r1 >>= function
  | `Apart ->
    ret None
  | _ ->
    global_env >>= fun env ->
    try
      (* TODO: hack, fix please *)
      let _ = GlobalEnv.restrict r0 r1 env in
      in_scope (Name.fresh ()) (`R (r0, r1)) m >>= fun x ->
      ret (Some x)
    with
    | I.Inconsistent ->
      ret None

let get_unsolved_holes =
  getl <<@> fun lcx ->
    Bwd.filter Entry.is_incomplete lcx

let abort_unsolved ~loc =
  get_unsolved_holes <<@> Bwd.length <<@> fun n ->
    if n > 0 then
      begin
        let pp fmt () =
          if n = 1
          then Format.fprintf fmt "1 unsolved hole"
          else Format.fprintf fmt "%i unsolved holes" n in
        Log.pp_message ~loc ~lvl:`Info pp Format.std_formatter ();
        exit 1
      end
