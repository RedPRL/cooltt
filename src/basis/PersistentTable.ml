module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val size : ('k, 'a) t -> int
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t
  val mem : 'k -> ('k, 'a) t -> bool
  val remove : 'k -> ('k, 'a) t -> ('k, 'a) t
  val set_opt : 'k -> 'a option -> ('k, 'a) t -> ('k, 'a) t
  val find : 'k -> ('k, 'a) t -> 'a option
  val fold : ('k -> 'a -> 'b -> 'b) -> ('k, 'a) t -> 'b -> 'b
  val merge : ('k, 'a) t -> ('k, 'a) t -> ('k, 'a) t
  val to_list : ('k, 'a) t -> ('k * 'a) list
  val to_list_keys : ('k, 'a) t -> 'k list
  val to_list_values : ('k, 'a) t -> 'a list
end

module M : S =
struct
  type ('k, 'a) t = ('k, 'a) node ref
  and ('k, 'a) node =
    | Tbl of ('k, 'a) Hashtbl.t
    | Diff of 'k * 'a option * ('k, 'a) t

  exception Fatal

  let init ~size =
    ref @@ Tbl (Hashtbl.create size)

  let raw_set_opt tbl k ov =
    match ov with
    | None -> Hashtbl.remove tbl k
    | Some v -> Hashtbl.replace tbl k v

  let rec reroot t =
    match !t with
    | Tbl _ ->
      ()
    | Diff (k, ov, t') ->
      reroot t';
      match !t' with
      | Tbl a as n ->
        let ov' = Hashtbl.find_opt a k in
        raw_set_opt a k ov;
        t := n;
        t' := Diff (k, ov', t)
      | _ ->
        raise Fatal
  
  let size t =
    reroot t;
    match !t with
    | Tbl a ->
      Hashtbl.length a
    | _ ->
      raise Fatal

  let get k t =
    reroot t;
    match !t with
    | Tbl a ->
      Hashtbl.find a k
    | _ ->
      raise Fatal

  let mem k t =
    reroot t;
    match !t with
    | Tbl a ->
      Hashtbl.mem a k
    | _ ->
      raise Fatal

  let find k t =
    try
      Some (get k t)
    with
    | _ -> None

  let set k v t =
    reroot t;
    match !t with
    | Tbl a as n ->
      let old = Hashtbl.find_opt a k in
      Hashtbl.replace a k v;
      let res = ref n in
      t := Diff (k, old, res);
      res
    | _ ->
      raise Fatal

  let remove k t =
    reroot t;
    match !t with
    | Tbl a as n ->
      let old = Hashtbl.find_opt a k in
      Hashtbl.remove a k;
      let res = ref n in
      t := Diff (k, old, res);
      res
    | _ ->
      raise Fatal

  let set_opt k ov t =
    match ov with
    | None -> remove k t
    | Some v -> set k v t

  let fold f t e =
    reroot t;
    match !t with
    | Tbl a ->
      Hashtbl.fold f a e
    | _ ->
      raise Fatal

  let merge t0 t1 = fold set t0 t1

  let to_list t =
    reroot t;
    match !t with
    | Tbl a ->
      List.of_seq (Hashtbl.to_seq a)
    | _ ->
      raise Fatal

  let to_list_keys t =
    reroot t;
    match !t with
    | Tbl a ->
      List.of_seq (Hashtbl.to_seq_keys a)
    | _ ->
      raise Fatal

  let to_list_values t =
    reroot t;
    match !t with
    | Tbl a ->
      List.of_seq (Hashtbl.to_seq_values a)
    | _ ->
      raise Fatal

end
