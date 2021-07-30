type 'a printer = Format.formatter -> 'a -> unit

module StringSet = Set.Make(String)

module Env =
struct
  (* [NOTE: Pretty Printer Environments]
     After some profiling, it turns out that we were spending
     a /huge/ amount of time generating fresh names + looking
     up DeBruijin indexed names. To avoid any sneaky O(n^2)
     behaviour, we use a sort of bump-allocator. *)
  type t = { names : string CCVector.vector;
             bound : int;
             used : StringSet.t }

  let emp : t = { names = CCVector.create (); bound = 0; used = StringSet.empty }

  let suffix_name nm i =
    if i == 0 then nm
    else nm ^ (Int.to_string i)

  (* [NOTE: Fresh Names]
     To find the "best" fresh name possible, we perform a sort of binary search.
     We start by checking 'x1, x2, x4, x8...' until we find some name that isn't
     in use yet. Once we have found this, we do a binary search between 'x{n}' and 'x{n*2 + 1}'
     to find the smallest name not yet in use.

     When the name we are trying to freshen already has a numeric suffix, (For instance: x4)
     we split the name into it's "base" and the suffix, and begin the search at the suffix
     rather than 0. *)


  (** Split a name into a base and a numerical suffix. *)
  let split_name (nm : string) : string * (int option) =
    let (pfx, sfx) = StringUtil.rpartition StringUtil.is_digit nm in
    (pfx, int_of_string_opt sfx)

  (** Compute the largest name still in use for a name. *)
  let lower_bound x env =
    let (base, n) = split_name x in
    let beg = Option.value n ~default:0 in
    let rec go i =
      if StringSet.mem (suffix_name base i) env.used then go (i * 2)
      else (base, i / 2)
    in
    go (beg + 1)

  let rec binary_search x lo hi env =
    let mid = lo + (hi - lo)/2 in
    let xmid = suffix_name x mid in
    if hi <= lo then xmid
    else if (StringSet.mem xmid env.used) then binary_search x (mid + 1) hi env
    else binary_search x lo mid env

  let rename x env =
    if StringSet.mem x env.used then
      let (base, u) = lower_bound x env in
      binary_search base u (u*2 + 1) env
    else x

  let var i (env : t) =
    if i < env.bound then
      (* As these are DeBrujin /indicies/, we need perform our look up from
         the back end of the bound section of the names. *)
      CCVector.get env.names (env.bound - i - 1)
    else
      failwith "Pp printer: tried to resolve bound variable out of range"

  let proj (env : t) : t =
    let nm = var (env.bound - 1) env in
    { env with bound = env.bound - 1; used = StringSet.remove nm env.used }

  let bind (env : t) (onm : string option) : string * t =
    let nm = Option.value ~default:"_x" onm in
    let rnm = rename nm env in
    let _ =
      if CCVector.length env.names <= env.bound
      then CCVector.push env.names rnm
      else CCVector.set env.names env.bound rnm
    in
    rnm, { env with bound = env.bound + 1; used = StringSet.add rnm env.used }

  let rec bindn (env : t) (nms : string option list) : string list * t =
    match nms with
    | [] ->
      [], env
    | nm :: nms ->
      let x, env' = bind env nm in
      let xs, env'' = bindn env' nms in
      (x :: xs), env''

  let names (env : t) : string list =
    CCSeq.to_list @@ CCSeq.take env.bound @@ CCVector.to_seq env.names
end

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

type env = Env.t
