type +'a trie = 'a Yuujinchou.Trie.t
type +'a t

val empty : 'a t
val map_view : f:('a trie -> 'a trie) -> 'a t -> 'a t
val map_export : f:('a trie -> 'a trie) -> 'a t -> 'a t
val fold : f:(view:'a trie -> export:'a trie -> 'b) -> 'a t -> 'b
val get_view : 'a t -> 'a trie
val get_export : 'a t -> 'a trie

module Result :
sig
  val map_view : f:('a trie -> ('a trie, 'error) result) -> 'a t -> ('a t, 'error) result
  val map_export : f:('a trie -> ('a trie, 'error) result) -> 'a t -> ('a t, 'error) result
end
