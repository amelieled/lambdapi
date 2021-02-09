
open Lplib.Extra
open Timed
   
open File_management.Error
open File_management.Module
open File_management.Pos
open File_management.Type
   
open Data_structure.Terms
open! Data_structure
open Data_structure.Sig_state

(** [find_sym ~prt ~prv b st qid] returns the symbol
    corresponding to the qualified identifier [qid]. If [fst qid.elt] is
    empty, we search for the name [snd qid.elt] in the opened modules of [st].
    The boolean [b] only indicates if the error message should mention
    variables, in the case where the module path is empty and the symbol is
    unbound. This is reported using the [Fatal] exception.
    {!constructor:Terms.expo.Protec} symbols from other modules
    are allowed in left-hand side of rewrite rules (only) iff [~prt] is true.
    {!constructor:Terms.expo.Privat} symbols are allowed iff [~prv]
    is [true]. *)
let find_sym : prt:bool -> prv:bool -> bool -> sig_state -> qident -> sym =
  fun ~prt ~prv b st qid ->
  let {elt = (mp, s); pos} = qid in
  let mp = List.map fst mp in
  let s =
    match mp with
    | []                               -> (* Symbol in scope. *)
        begin
          try fst (StrMap.find s st.in_scope) with Not_found ->
          let txt = if b then " or variable" else "" in
          fatal pos "Unbound symbol%s [%s]." txt s
        end
    | [m] when StrMap.mem m st.aliases -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try PathMap.find (StrMap.find m st.aliases) Timed.(!Sign.loaded)
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
    | _                                -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (PathMap.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." Path.pp mp;
          (* The signature must have been loaded. *)
          let sign =
            try PathMap.find mp Timed.(!Sign.loaded)
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
  in
  match (prt, prv, s.sym_expo) with
  | (false, _    , Protec) ->
      if s.sym_path = st.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
