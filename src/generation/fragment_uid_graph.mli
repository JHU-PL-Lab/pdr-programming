open Jhupllib;;

open Pdr_programming_continuation_extensions.Fragment_types;;

module Fragment_uid_fragment_uid_multimap :
  Multimap.Multimap_sig with type key = Fragment_uid.t
                         and type value = Fragment_uid.t
;;

val create_reverse_uid_graph :
  fragment_group -> Fragment_uid_fragment_uid_multimap.t;;

type toposort_mark = Unmarked | In_progress | Complete;;
exception Cyclic_graph_in_topological_sort;;

val topological_sort :
  Fragment_uid_fragment_uid_multimap.t -> Fragment_uid.t list
