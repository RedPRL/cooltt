open Basis
open Bwd
open Frontend
open Core
open CodeUnit
open Cubical

module S = Syntax
module D = Domain

open Lsp.Types
module Json = Lsp.Import.Json

module LwtIO = Lwt_io

open LspLwt.Notation

(* FIXME: This should live elsewhere, we use this a lot. *)
let ppenv_bind env ident =
  Pp.Env.bind env @@ Ident.to_string_opt ident

module Visualize = struct
  let command_name = "cooltt.visualize"
  let action_kind = CodeActionKind.Other "cooltt.visualize.hole"

  let serialize_label (str : string) (pos : (string * float) list) : Json.t =
    `Assoc [
      "position", `Assoc (List.map (fun (nm, d) -> (nm, `Float d)) pos);
      "txt", `String str
    ]

  let dim_tm : S.t -> float =
    function
    | S.Dim0 -> -. 1.0
    | S.Dim1 -> 1.0
    | _ -> failwith "dim_tm: bad dim"

  let rec dim_from_cof (dims : (string option) bwd) (cof : S.t) : (string * float) list list =
    match cof with
    | S.Cof (Cof.Eq (S.Var v, r)) ->
      let axis = Option.get @@ Bwd.nth dims v in
      let d = dim_tm r in
      [[(axis, d)]]
    | S.Cof (Cof.Join cofs) -> List.concat_map (dim_from_cof dims) cofs
    | S.Cof (Cof.Meet cofs) -> [List.concat @@ List.concat_map (dim_from_cof dims) cofs]
    | _ -> failwith "dim_from_cof: bad cof"

  let boundary_labels dims env bdry =
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
    match bdry with
    | S.CofSplit branches ->
      let (_x, envx) = ppenv_bind env `Anon in
      List.concat_map (go envx dims) branches
    | _ -> []

  let serialize_boundary ctx goal : Json.t option =
    let rec go dims env =
      function
      | [] ->
        begin
          match goal with
          | S.Sub (_, _, bdry) ->
            let dim_names = Bwd.to_list @@ Bwd.filter_map (Option.map (fun name -> `String name)) dims in
            let labels = boundary_labels dims env bdry in
            let context = Format.asprintf "%a" (S.pp_sequent ~lbl:None ctx) goal in
            let msg = `Assoc [
                ("dims", `List dim_names);
                ("labels", `List labels);
                ("context", `String context)
              ]
            in Some (`Assoc ["DisplayGoal", msg])
          | _ -> None
        end
      | (var, var_tp) :: ctx ->
        let (dim_name, envx) = ppenv_bind env var in
        match var_tp with
        | S.TpDim -> go (Snoc (dims, Some dim_name)) envx ctx
        | _ -> go (Snoc (dims, None)) envx ctx
    in go Emp Pp.Env.emp ctx

  let create ctx goal =
    serialize_boundary ctx goal |> Option.map @@ fun json ->
    let command = Command.create
        ~title:"visualize"
        ~command:command_name
        ~arguments:[json]
        ()
    in CodeAction.create
      ~title:"visualize hole"
      ~kind:action_kind
      ~command
      ()

  let execute arguments =
    match arguments with
    | Some [arg] ->
      (* FIXME: Handle the visualizer socket better *)
      let host = Unix.gethostbyname "localhost" in
      let host_entry = Array.get host.h_addr_list 0 in
      let addr = Unix.ADDR_INET (host_entry, 3001) in
      let* (ic, oc) = LwtIO.open_connection addr in
      let* _ = LwtIO.write oc (Json.to_string arg) in
      let* _ = LwtIO.flush oc in
      let* _ = LwtIO.close ic in
      LwtIO.close oc
    | _ ->
      (* FIXME: Handle this better *)
      Lwt.return ()
end
