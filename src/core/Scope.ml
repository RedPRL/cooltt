module Y = Yuujinchou
module YT = Y.Trie

type 'a trie = 'a YT.t
type 'a t =
  { view : 'a YT.t
  ; export : 'a YT.t
  }

let empty = {view = YT.empty; export = YT.empty}
let map_view ~f s = {s with view = f s.view}
let map_export ~f s = {s with export = f s.export}
let fold ~f s = f ~view:s.view ~export:s.export
let get_view s = s.view
let get_export s = s.export

module Result =
struct
  let map_view ~f s =
    Result.bind (f s.view) @@ fun view -> Result.ok {s with view}
  let map_export ~f s =
    Result.bind (f s.export) @@ fun export -> Result.ok {s with export}
end
