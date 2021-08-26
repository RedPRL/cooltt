open Basis
open Bwd

open Core
open CodeUnit
open Cubical

module S = Syntax

module J = Ezjsonm

(* [NOTE: Cooltt Server]
   We use a 'ref' here to prevent having to thread down a server handle
   deep into the guts of the elaborator. *)
let server : Unix.file_descr option ref =
  ref None

let init port =
  try
    Format.eprintf "Initializing cooltt server connection on port %n...@." port;
    let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let localhost = Unix.inet_addr_of_string "127.0.0.1" in
    let () = Unix.connect socket (Unix.ADDR_INET (localhost, port)) in
    Format.eprintf "Cooltt server connection initialized@.";
    server := Some socket
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

let serialize_label (n : int) (str : string) (axes : (int * float) list) : J.value =
  let pos = Array.make n (J.float 0.0) in
  let _ = axes |> List.iter @@ fun (dim, p) ->
    Array.set pos dim (J.float p)
  in
  `O [("position", `A (Array.to_list pos)); ("txt", `String str)]

let dim_tm : S.t -> float =
  function
  | S.Dim0 -> -. 1.0
  | S.Dim1 -> 1.0
  | _ -> failwith "dim_tm: bad dim"

(* Fetch a list of label positions from a cofibration. *)
let rec dim_from_cof (dims : (int option) bwd) (cof : S.t) : (int * float) list list =
  match cof with
  | S.Cof (Cof.Eq (S.Var v, r)) ->
    let axis = Option.get @@ Bwd.nth dims v in
    let d = dim_tm r in
    [[(axis, d)]]
  | S.Cof (Cof.Join cofs) -> List.concat_map (dim_from_cof dims) cofs
  | S.Cof (Cof.Meet cofs) -> [List.concat @@ List.concat_map (dim_from_cof dims) cofs]
  | _ -> failwith "dim_from_cof: bad cof"

(* Create our list of labels from a boundary constraint. *)
let boundary_labels (num_dims : int) (dims : (int option) bwd) (env : Pp.env) (tm : S.t) : J.value list =
  let rec go env dims (bdry, cons) =
    match cons with
    | S.CofSplit branches ->
      let (_x, envx) = ppenv_bind env `Anon in
      List.concat_map (go envx (Snoc (dims, None))) branches
    | _ ->
      let (_x, envx) = ppenv_bind env `Anon in
      let lbl = Format.asprintf "%a" (S.pp envx) cons in
      List.map (serialize_label num_dims lbl) @@ dim_from_cof (Snoc (dims, None)) bdry
  in
  match tm with
  | S.CofSplit branches ->
    let (_x, envx) = ppenv_bind env `Anon in
    List.concat_map (go envx dims) branches
  | _ -> []

let serialize_boundary (ctx : (Ident.t * S.tp) list) (goal : S.tp) : J.t option =
  let rec go dim_count dims env =
    function
    | [] ->
      begin
        match goal with
        | S.Sub (_, _, bdry) ->
          let num_dims = Bwd.length @@ Bwd.filter Option.is_some dims in
          let labels = boundary_labels num_dims dims env bdry in
          let context = Format.asprintf "%a" (S.pp_sequent ~lbl:None ctx) goal in
          let msg = `O [
              ("dim", J.float @@ Int.to_float num_dims);
              ("labels", `A labels);
              ("context", `String context)
            ] in
          Some (`O [("DisplayGoal", msg)])
        | _ -> None
      end
    | (var, var_tp) :: ctx ->
      let (_x, envx) = ppenv_bind env var in
      match var_tp with
      | S.TpDim -> go (dim_count + 1) (Snoc (dims, Some dim_count)) envx ctx
      | _ -> go dim_count (Snoc (dims, None)) envx ctx
  in go 0 Emp Pp.Env.emp ctx

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
