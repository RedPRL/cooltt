open Basis
open Bwd

module K = Kado.Syntax

open Core
open CodeUnit

module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module R = Refiner
module RM = RefineMonad
module J = Ezjsonm
module Y = Yojson.Safe

open Monad.Notation (RM)
module M = Monad.Util (RM)

(* [NOTE: Cooltt Server]
   We use a 'ref' here to prevent having to thread down a server handle
   deep into the guts of the elaborator. *)
let server : Unix.file_descr option ref =
  ref None
let init host_name port =
  try
    Format.eprintf "Initializing cooltt server connection on port %n...@." port;
    let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let host_entry = Unix.gethostbyname host_name in
    begin
      match CCArray.get_safe host_entry.h_addr_list 0 with
      | Some addr ->
        let () = Unix.connect socket (Unix.ADDR_INET (addr, port)) in
        Format.eprintf "Cooltt server connection initialized@.";
        server := Some socket
      | None -> Format.eprintf "Error: Could not initialize cooltt server connection.@."
    end
  with Unix.Unix_error _ ->
    Format.eprintf "Error: Could not initialize cooltt server connection.@."

let close () =
  match !server with
  | Some socket ->
    Unix.close socket;
    server := None
  | None -> ()

let ppenv_bind env ident =
  Pp.Env.bind env @@ Ident.to_string_opt ident

let serialize_label (str : string) (pos : (string * float) list) : J.value =
  `O [("position", `O (List.map (fun (nm, d) -> (nm, J.float d)) pos)); ("txt", `String str)]

let dim_tm : S.t -> float =
  function
  | S.Dim0 -> -. 1.0
  | S.Dim1 -> 1.0
  | _ -> failwith "dim_tm: bad dim"

(* Fetch a list of label positions from a cofibration. *)
let rec dim_from_cof (dims : (string option) bwd) (cof : S.t) : (string * float) list list =
  match cof with
  | S.Cof (K.Le (S.Var v, r))
  | S.Cof (K.Le (r, S.Var v)) ->
    let axis = Option.get @@ BwdLabels.nth dims v in
    let d = dim_tm r in
    [[(axis, d)]]
  | S.Cof (K.Join cofs) -> List.concat_map (dim_from_cof dims) cofs
  | S.Cof (K.Meet cofs) -> [List.concat @@ List.concat_map (dim_from_cof dims) cofs]
  | cof ->
    failwith @@ Format.asprintf "dim_from_cof: bad cof '%a'" S.dump cof

(* Create our list of labels from a boundary constraint. *)
let boundary_labels (dims : (string option) bwd) (env : Pp.env) (cof : S.t) (tm : S.t) : J.value list =
  let rec go env dims (bdry, cons) =
    match cons with
    | S.CofSplit branches ->
      let (_x, envx) = ppenv_bind env Ident.anon in
      List.concat_map (go envx (Snoc (dims, None))) branches
    | _ ->
      let (_x, envx) = ppenv_bind env Ident.anon in
      let lbl = Format.asprintf "%a" (S.pp envx) cons in
      List.map (serialize_label lbl) @@ dim_from_cof (Snoc (dims, None)) bdry
  in
  let (_, envx) = ppenv_bind env Ident.anon in
  match tm with
  | S.CofSplit branches -> 
    List.concat_map (go envx dims) branches
  | _ ->
    let lbl = Format.asprintf "%a" (S.pp envx) tm in
    List.map (serialize_label lbl) @@ dim_from_cof dims cof

let rec type_labels dims env tp =
  let rec unpack_bdry_lam tm env =
    match tm with
    | S.Lam (var, body) ->
      let (_, envx) = ppenv_bind env var in
      unpack_bdry_lam body envx
    | _ -> tm, env
  in
  match tp with
  | S.Sub (_, cof, tm) ->
    boundary_labels dims env cof tm
  | S.El (S.CodeExt (_, cof, _, bdry_lam)) ->
    let (tm, envx) = unpack_bdry_lam bdry_lam env in
    boundary_labels dims envx cof tm
  | S.Pi (dom, var, cod) ->
    let (dim_name, envx) = ppenv_bind env var in
    begin
      match dom with
      | S.TpDim -> type_labels (Snoc (dims, Some dim_name)) envx cod
      | _ -> type_labels (Snoc (dims, None)) envx cod
    end      
  | _ -> []

let context_labels (ctx : (Ident.t * S.tp) list) (env : Pp.env) : J.value list =
  let serialize_cube id dims labels =
    let dim_names = BwdLabels.to_list @@ BwdLabels.filter_map ~f:Fun.id dims in
    `O [
      ("id", `String (Ident.to_string id));
      ("dims", `A (List.map J.string dim_names));
      ("labels", `A labels) 
    ]
  in
  let run dims env (id, tp) =
    serialize_cube id dims @@ type_labels dims env tp
  in List.map (run Emp env) ctx

let ppenv_bind_ctx (ctx : (Ident.t * S.tp) list) (env : Pp.env) : string option bwd * Pp.env =
  let rec go dims env =
    function
    | [] -> (dims, env)
    | (var, var_tp) :: ctx ->
      let (dim_name, envx) = ppenv_bind env var in
      match var_tp with
      | S.TpDim -> go (Snoc (dims, Some dim_name)) envx ctx
      | _ -> go (Snoc (dims, None)) envx ctx
  in go Emp env ctx

let serialize_boundary (ctx : (Ident.t * S.tp) list) (goal : S.tp) : J.t option =
  let (dims, env) = ppenv_bind_ctx ctx Pp.Env.emp in
  match goal with
  | S.Sub (_, cof, tm) ->
    let dim_names = BwdLabels.to_list @@ BwdLabels.filter_map ~f:Fun.id dims in
    let labels = boundary_labels dims env cof tm in
    let context = Format.asprintf "%a" (S.pp_sequent ~lbl:None ctx) goal in
    let ctx_labels = context_labels ctx env in
    let msg = `O [
        ("dims", `A (List.map J.string dim_names));
        ("labels", `A labels);
        ("context", `String context);
        ("cubes", `A ctx_labels)
      ] in
    Some (`O [("DisplayGoal", msg)])
  | _ -> None

(* Sends the current context and goal to the server. *)
let dispatch_goal ctx goal =
  match !server, serialize_boundary ctx goal with
  | Some socket, Some msg ->
    begin
      try
        let buf = Buffer.create 65536 in
        J.to_buffer ~minify:true buf msg;
        let nbytes = Unix.send socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
        Debug.print "dispatch_goal: Sent %n bytes to Server.@." nbytes;
        ()
      with Unix.Unix_error _ ->
        Format.eprintf "Cooltt server connection lost.@.";
        close ()
    end
  | _, _ -> ()

let serialize_faces ctx goals =  
  let (dims, env) = ppenv_bind_ctx ctx Pp.Env.emp in
  let serialize_goal (tp, phi, _) =
    let* tp = RM.quote_tp tp in
    let* phi = RM.quote_cof phi in
    let lbl = Format.asprintf "%a" (S.pp_tp env) tp in
    let pos = dim_from_cof dims phi in
    RM.ret @@ `A (List.map (serialize_label lbl) pos)
  in
  let* ser = M.map serialize_goal goals in
  RM.ret @@ `O [("EditGoal", `A ser)]

(* Sends the faces of the cube (holes in the hcom) to the server, and blocks until the server
   sends a ConcreteSyntax. This then gets elaborated. *)
let send_faces ctx goals =
  let* msg = serialize_faces ctx goals in
  match !server with
  | Some socket ->
    begin
      try
        let buf = Buffer.create 65536 in
        J.to_buffer ~minify:true buf msg;
        let nbytes = Unix.send socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
        Debug.print "send_faces: Sent %n bytes to Server.@." nbytes;
        Buffer.clear buf;
        let nbytes = Unix.recv socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
        Debug.print "send_faces: Received %n bytes from Server.@." nbytes;
        RM.ret @@ Some (CS.con_of_yojson @@ Y.from_string @@ Buffer.contents buf)
      with Unix.Unix_error _ ->
        Format.eprintf "Cooltt server connection lost.@.";
        close ();
        RM.ret None
    end
  | _ -> RM.ret None
