open Basis
open Bwd

module K = Kado.Syntax

open Core
open CodeUnit

module S = Syntax

module J = Ezjsonm

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
  | S.Cof (K.Le (S.Var v, r)) ->
    let axis = Option.get @@ BwdLabels.nth dims v in
    let d = dim_tm r in
    [[(axis, d)]]
  | S.Cof (K.Join cofs) -> List.concat_map (dim_from_cof dims) cofs
  | S.Cof (K.Meet cofs) -> [List.concat @@ List.concat_map (dim_from_cof dims) cofs]
  | _ -> failwith "dim_from_cof: bad cof"

(* Create our list of labels from a boundary constraint. *)
let boundary_labels (dims : (string option) bwd) (env : Pp.env) (tm : S.t) : J.value list =
  let rec go env dims (bdry, cons) =
    match cons with
    | S.CofSplit branches ->
      let (_x, envx) = ppenv_bind env `Anon in
      List.concat_map (go envx (Snoc (dims, None))) branches
    | _ ->
      let (_x, envx) = ppenv_bind env `Anon in
      let lbl = Format.asprintf "%a" (S.pp envx) cons in
      List.map (serialize_label lbl) @@ dim_from_cof (Snoc (dims, None)) bdry
  in
  match tm with
  | S.CofSplit branches ->
    let (_x, envx) = ppenv_bind env `Anon in
    List.concat_map (go envx dims) branches
  | _ -> []

let serialize_boundary (ctx : (Ident.t * S.tp) list) (goal : S.tp) : J.t option =
  let rec go dims env =
    function
    | [] ->
      begin
        match goal with
        | S.Sub (_, _, bdry) ->
          let dim_names = BwdLabels.to_list @@ BwdLabels.filter_map ~f:Fun.id dims in
          let labels = boundary_labels dims env bdry in
          let context = Format.asprintf "%a" (S.pp_sequent ~lbl:None ctx) goal in
          let msg = `O [
              ("dims", `A (List.map J.string dim_names));
              ("labels", `A labels);
              ("context", `String context)
            ] in
          Some (`O [("DisplayGoal", msg)])
        | _ -> None
      end
    | (var, var_tp) :: ctx ->
      let (dim_name, envx) = ppenv_bind env var in
      match var_tp with
      | S.TpDim -> go (Snoc (dims, Some dim_name)) envx ctx
      | _ -> go (Snoc (dims, None)) envx ctx
  in go Emp Pp.Env.emp ctx

let dispatch_goal ctx goal =
  match !server, serialize_boundary ctx goal with
  | Some socket, Some msg ->
    begin
      try
        let buf = Buffer.create 65536 in
        J.to_buffer ~minify:true buf msg;
        let nbytes = Unix.send socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
        Debug.print "Sent %n bytes to Server.@." nbytes;
        ()
      with Unix.Unix_error _ ->
        Format.eprintf "Cooltt server connection lost.@.";
        close ()
    end
  | _, _ -> ()
