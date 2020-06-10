open CoolBasis
open Bwd

module CS = ConcreteSyntax
module S = Syntax
module D = Domain

module M = Monad.Notation (Incremental)
open M
module MU = Monad.Util (Incremental)
module J = Ezjsonm

exception Todo

module BasicJSON =
struct

  let ret = Incremental.ret (* todo this can't be right ... can it? *)

  let json_of_int (i : int) : [> `String of string ] =
    `String (string_of_int i)

  let int_of_json : [> `String of string ] -> int =
    function
    | `String s -> int_of_string s
    | j -> J.parse_error j "int_of_json"

  let json_of_string = `String (* todo/iev this may need to be η-expanded for ocaml reasons *)

  let string_of_json =
    function
    | `String s -> s
    | j -> J.parse_error j "string_of_json"

  let json_of_ostring =
    function
    | None -> `Null
    | Some str -> `String str

  let ostring_of_json =
    function
    | `Null -> None
    | `String str -> Some str
    | j -> J.parse_error j "ostring_of_json"

  let json_of_list json_of_item l =
     MU.traverse json_of_item l <<@> fun l -> `A l

  let list_of_json item_of_json =
    function
    | `A l -> MU.traverse item_of_json l
    | j -> J.parse_error j "list_of_json"

  (* pure version *)
  let json_of_list_ json_of_item l =
    `A (List.map json_of_item l)

  (* pure version *)
  let list_of_json_ item_of_json =
    function
    | `A l -> List.map item_of_json l
    | j -> J.parse_error j "list_of_json_"

  let json_of_ostring_bwd nms =
    json_of_list_ json_of_ostring @@ Bwd.to_list nms

  let ostring_bwd_of_json l =
    Bwd.from_list @@ list_of_json_ ostring_of_json l

  let json_of_pair (json_of_a, json_of_b) (a, b) =
    json_of_a a >>= fun a ->
    json_of_b b >>= fun b ->
    ret @@ `A [a; b]

  let pair_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      a_of_json a >>= fun a ->
      b_of_json b >>= fun b ->
      ret @@ (a, b)
    | j -> J.parse_error j "pair_of_json"

  let json_of_labeled (json_of_a, json_of_b) (a, b) =
    json_of_b b >>= fun b ->
    ret @@ `A [json_of_a a; b]

  let labeled_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      b_of_json b >>= fun b ->
      ret @@ (a_of_json a, b)
    | j -> J.parse_error j "labeled_of_json"

  (* labeled in reverse *)
  let json_of_delebal (json_of_a, json_of_b) (a, b) =
    json_of_a a >>= fun a ->
    ret @@ `A [a; json_of_b b]

  (* labeled in reverse *)
  let delebal_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      a_of_json a >>= fun a ->
      ret @@ (a, b_of_json b)
    | j -> J.parse_error j "delebal_of_json"

end

module TmJSON =
struct
  open BasicJSON

  open SyntaxData

  let json_of_sym = fun _ -> raise Todo
  let json_of_name = fun _ -> raise Todo

  let rec json_of_tm : t -> J.value m =
    function
    | Var x -> ret @@ `A [`String "Var";  json_of_int x]

    | Global sym ->
      json_of_sym sym >>= fun sym ->
      ret @@ `A [`String "Global"; sym]

    | Let (t1 , nm , t2) ->
      json_of_tm t1 >>= fun t1 ->
      json_of_name nm >>= fun nm ->
      json_of_tm t2 >>= fun t2 ->
      ret @@ `A [`String "Let"; t1; nm; t2]

    | Ann (tm, tp) ->
      json_of_tm tm >>= fun tm ->
      json_of_tp tp >>= fun tp ->
      ret @@ `A [`String "Ann"; tm; tp]

    | Zero -> ret @@ `A [`String "Zero"]
    | Suc n ->
      json_of_tm n >>= fun n ->
      ret @@ `A [`String "Suc"; n]

    | NatElim (tm1, tm2, tm3, tm4) ->
      json_of_tm tm1 >>= fun tm1 ->
      json_of_tm tm2 >>= fun tm2 ->
      json_of_tm tm3 >>= fun tm3 ->
      json_of_tm tm4 >>= fun tm4 ->
      ret @@ `A [`String "NatElim"; tm1; tm2; tm3; tm4]

    | Base -> raise Todo
    | Loop tm -> raise Todo
    | CircleElim (tm1, tm2, tm3, tm4) -> raise Todo

    | Lam (nm, tm)  -> raise Todo
    | Ap (tm1, tm2) -> raise Todo

    | Pair (tm1, tm2)  -> raise Todo
    | Fst tm -> raise Todo
    | Snd tm -> raise Todo

    | GoalRet tm -> raise Todo
    | GoalProj tm -> raise Todo

    | Coe (tm1, tm2, tm3, tm4) -> raise Todo
    | HCom (tm1, tm2, tm3, tm4, tm5) -> raise Todo
    | Com (tm1, tm2, tm3, tm4, tm5) -> raise Todo

    | SubIn tm -> raise Todo
    | SubOut tm -> raise Todo

    | Dim0 -> raise Todo
    | Dim1 -> raise Todo
    | Cof c -> raise Todo (* todo here this requires serializing cofs too *)
    | ForallCof tm -> raise Todo
    | CofSplit cs -> raise Todo
    | Prf -> raise Todo

    | ElIn tm -> raise Todo
    | ElOut tm -> raise Todo

    | Box (tm1, tm2, tm3, tm4, tm5) -> raise Todo
    | Cap (tm1, tm2, tm3, tm4, tm5) -> raise Todo

    | VIn (tm1, tm2, tm3, tm4) -> raise Todo
    | VProj (tm1, tm2, tm3, tm4, tm5) -> raise Todo

    | CodeExt (i, tm1, glo, tm2) -> raise Todo
    | CodePi (tm1, tm2) -> raise Todo
    | CodeSg (tm1, tm2) -> raise Todo
    | CodeNat -> raise Todo
    | CodeUniv -> raise Todo
    | CodeV (tm1, tm2, tm3, tm4) -> raise Todo
    | CodeCircle -> raise Todo

    | ESub(s,tm) -> raise Todo

  and json_of_tp : tp -> J.value m =
    function
    | Univ -> raise Todo
    | El(tp) -> raise Todo
    | TpVar(i) -> raise Todo
    | GoalTp (name, tp) -> raise Todo
    | TpDim -> raise Todo
    | TpCof -> raise Todo
    | TpPrf tp -> raise Todo
    | TpCofSplit l -> raise Todo
    | Sub (tp, t1, t2) -> raise Todo
    | Pi (tp1, nm, tp2) -> raise Todo
    | Sg (tp1, nm, tp2) -> raise Todo
    | Nat -> raise Todo
    | Circle -> raise Todo
    | TpESub (sub, tp) -> raise Todo

  and json_of_sub : sub -> J.value m =
    function
    | Sb0 -> raise Todo
    | SbI -> raise Todo
    | SbE (s, t) -> raise Todo
    | SbP -> raise Todo
    | SbC (s1, s2) -> raise Todo

  and json_of_env : env -> J.value = fun _ -> raise Todo

end
