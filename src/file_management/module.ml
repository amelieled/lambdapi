(** Path utilities. *)

open Lplib
open Lplib.Base
open Lplib.Extra

open Error

(** Logging function for evaluation. *)
let log_file = new_logger 'f' "file" "file system"
let log_file = log_file.logger

(** Representation of module paths and related operations. *)
module Path =
  struct
    (** Representation of a module path (roughly, a file path). *)
    type module_path = string list

    (** Short synonym of [module_path]. *)
    type t = module_path

    (** [compare] is a standard comparing function for module paths. *)
    let compare : t -> t -> int = Stdlib.compare

    (** [pp oc mp] prints [mp] to channel [oc]. *)
    let pp : module_path pp = fun oc mp ->
      Format.pp_print_string oc (String.concat "." mp)

    (** [check_simple mp] Checks that [mp] is a “simple” module path, that is,
        that its members are of the form ["[a-zA-Z_][a-zA-Z0-9_]*"]. *)
    let check_simple : t -> unit = fun mod_path ->
      let fail fmt =
        fatal_msg "The (simple) module path [%a] is ill-formed: " pp mod_path;
        fatal_no_pos fmt
      in
      let valid_path_member s =
        if String.length s = 0 then fail "empty module path member.";
        for i = 0 to String.length s - 1 do
          match String.get s i with
          | 'a'..'z' | 'A'..'Z' | '_' -> ()
          | '0'..'9' when i <> 0      -> ()
          | _                         -> fail "invalid path member [%s]." s
        done
      in
      List.iter valid_path_member mod_path

    (** [ghost s] creates a special module path for module of name [s]. Ghost
        modules cannot be handled by the user. *)
    let ghost : string -> t = fun s -> [""; s]
  end

(** Functional maps with module paths as keys. *)
module PathMap = Map.Make(Path)

(** Synonym of [string] for file paths. *)
type file_path = string

(** Representation of the mapping from module paths to files. *)
module ModMap :
  sig
    (** Module path mapping. *)
    type t

    (** [empty] is an empty module path mapping. *)
    val empty : t

    (** Exception raised if an attempt is made to map an already mapped module
        (including the root). *)
    exception Already_mapped

    (** [set_root path m] sets the library root of [m] to be [path].
        @raise Already_mapped if library root of [m] is already set. *)
    val set_root : file_path -> t -> t

    (** [add mp path m] extends the mapping [m] by associating the module path
        [mp] to the file path [path].
        @raise Already_mapped when [mp] is already mapped in [m]. *)
    val add : Path.t -> file_path -> t -> t

    (** Exception raised if an attempt is made to use the [get] function prior
        to the root being set (using [set_root]). *)
    exception Root_not_set

    (** [get mp m] obtains the file path corresponding to the module path [mp]
        in [m] (with no particular extension).
        @raise Root_not_set when the root of [m] has not been set using
        [set_root].  *)
    val get : Path.t -> t -> file_path

    (** [iter fn m] calls function [fn] on every binding stored in [m]. *)
    val iter : (Path.t -> file_path -> unit) -> t -> unit
  end =
  struct
    type t = Node of file_path option * t StrMap.t

    let empty = Node(None, StrMap.empty)

    exception Already_mapped

    let set_root path (Node(po, m)) =
      match po with
      | None    -> Node(Some(path), m)
      | Some(_) -> raise Already_mapped

    let rec singleton ks path =
      match ks with
      | []      -> Node(Some(path), StrMap.empty)
      | k :: ks -> Node(None, StrMap.singleton k (singleton ks path))

    let rec add ks path (Node(po, m)) =
      match (po, ks) with
      | (Some(_), []     ) -> raise Already_mapped
      | (None   , []     ) -> Node(Some(path), m)
      | (_      , k :: ks) ->
          try Node(po, StrMap.add k (add ks path (StrMap.find k m)) m)
          with Not_found -> Node(po, StrMap.add k (singleton ks path) m)

    exception Root_not_set

    let get ks (Node(po, m)) =
      let rec get (root, old_ks) ks m =
        match ks with
        | []      ->
            List.fold_left Filename.concat root old_ks
        | k :: ks ->
            match StrMap.find k m with
            | Node(Some(root), m) -> get (root, ks) ks m
            | Node(None      , m) -> get (root, old_ks) ks m
            | exception Not_found ->
                List.fold_left Filename.concat root old_ks
      in
      match po with
      | None       -> raise Root_not_set
      | Some(root) -> get (root, ks) ks m

    let iter fn m =
      let rec iter path (Node(po, m)) =
        Option.iter (fun file -> fn path file) po;
        StrMap.iter (fun k m -> iter (path @ [k]) m) m
      in
      iter [] m
  end
