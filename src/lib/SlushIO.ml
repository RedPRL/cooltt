open CoolBasis

module CS = ConcreteSyntax
module S = Syntax
module D = Domain

module M = Monad.Notation (Contextual)
open M
module MU = Monad.Util (Contextual)
module J = Ezjsonm

exception Todo


module BasicJson =
struct

  let json_of_int i = `String (string_of_int i)

  let int_of_json =
    function
    | `String s -> int_of_string s
    | j -> J.parse_error j "int_of_json"

  let json_of_string s = `String s

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

let rec json_of_term tm = raise Todo
and json_of_tp tp = raise Todo
