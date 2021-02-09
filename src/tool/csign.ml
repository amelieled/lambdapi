(** Signature utilities for compilation. *)

open! Lplib
open Lplib.Extra

(*open! Parsing*)
   
open Timed
open File_management.Error
open File_management.Module
open Data_structure.Terms

open Data_structure.Sign

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term t =
    let link_binder b =
      let (x,t) = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term t)))
    in
    match unfold t with
    | Vari(_)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s)     -> Symb(link_symb s)
    | Prod(a,b)   -> Prod(link_term a, link_binder b)
    | Abst(a,t)   -> Abst(link_term a, link_binder t)
    | LLet(a,t,u) -> LLet(link_term a, link_term t, link_binder u)
    | Appl(t,u)   -> Appl(link_term t, link_term u)
    | Meta(_,_)   -> assert false
    | Patt(i,n,m) -> Patt(i, n, Array.map link_term m)
    | TEnv(t,m)   -> TEnv(t, Array.map link_term m)
    | Wild        -> t
    | TRef(_)     -> t
  and link_rule r =
    let lhs = List.map link_term r.lhs in
    let (xs, rhs) = Bindlib.unmbind r.rhs in
    let rhs = lift (link_term rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    if s.sym_path = sign.sign_path then s else
    try
      let sign = PathMap.find s.sym_path !loaded in
      try find sign s.sym_name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ (s,_) =
    s.sym_type  := link_term !(s.sym_type);
    s.sym_def   := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn path ls =
    let sign =
      try PathMap.find path !loaded
      with Not_found -> assert false
    in
    let h (n, r) =
      let r = link_rule r in
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ [r]
    in
    List.iter h ls
  in
  PathMap.iter gn !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  let lsy (sym, h) = link_symb sym, h in
  sign.sign_notations :=
    (* Keys of the mapping are linked *)
    SymMap.to_seq !(sign.sign_notations) |>
    Seq.map lsy |> SymMap.of_seq;
  StrMap.iter (fun _ (s, _) -> Data_structure.Tree.update_dtree s) !(sign.sign_symbols);
  let link_inductive i =
    { ind_cons = List.map link_symb i.ind_cons
    ; ind_prop = link_symb i.ind_prop }
  in
  let fn s i m = SymMap.add (link_symb s) (link_inductive i) m in
  sign.sign_ind := SymMap.fold fn !(sign.sign_ind) SymMap.empty

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    s.sym_tree := Data_structure.Tree_types.empty_dtree ;
    if s.sym_path <> sign.sign_path then
      (s.sym_type := Kind; s.sym_rules := [])
  in
  let rec unlink_term t =
    let unlink_binder b = unlink_term (snd (Bindlib.unbind b)) in
    let unlink_term_env t =
      match t with
      | TE_Vari(_) -> ()
      | _          -> assert false (* Should not happen, matching-specific. *)
    in
    match unfold t with
    | Vari(_)      -> ()
    | Type         -> ()
    | Kind         -> ()
    | Symb(s)      -> unlink_sym s
    | Prod(a,b)    -> unlink_term a; unlink_binder b
    | Abst(a,t)    -> unlink_term a; unlink_binder t
    | LLet(a,t,u)  -> unlink_term a; unlink_term t; unlink_binder u
    | Appl(t,u)    -> unlink_term t; unlink_term u
    | Meta(_,_)    -> assert false (* Should not happen, uninstantiated. *)
    | Patt(_,_,_)  -> () (* The environment only contains variables. *)
    | TEnv(t,m)    -> unlink_term_env t; Array.iter unlink_term m
    | Wild         -> ()
    | TRef(_)      -> ()
  and unlink_rule r =
    List.iter unlink_term r.lhs;
    let (_, rhs) = Bindlib.unmbind r.rhs in
    unlink_term rhs
  in
  let fn _ (s,_) =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn _ ls = List.iter (fun (_, r) -> unlink_rule r) ls in
  PathMap.iter gn !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  SymMap.iter (fun s _ -> unlink_sym s) !(sign.sign_notations);
  let unlink_inductive i =
    List.iter unlink_sym i.ind_cons; unlink_sym i.ind_prop
  in
  let fn s i = unlink_sym s; unlink_inductive i in
  SymMap.iter fn !(sign.sign_ind)

(** [strip_private sign] removes private symbols from signature [sign]. *)
let strip_private : t -> unit = fun sign ->
  let not_prv sym = not (Data_structure.Terms.is_private sym) in
  sign.sign_symbols :=
    StrMap.filter (fun _ s -> not_prv (fst s)) !(sign.sign_symbols);
  sign.sign_notations :=
    Data_structure.Terms.SymMap.filter (fun s _ -> not_prv s) !(sign.sign_notations)

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; exit 0
  | i -> ignore (Unix.waitpid [] i)

(* NOTE [Unix.fork] is used to safely [unlink] and write an object file, while
   preserving a valid copy of the written signature in the parent process. *)

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
let read : string -> t = fun fname ->
  let ic = open_in fname in
  let sign =
    try
      let sign = Marshal.from_channel ic in
      close_in ic; sign
    with Failure _ ->
      close_in ic;
      fatal_no_pos "File [%s] is incompatible with current binary...\n" fname
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  let reset_timed_refs sign =
    unsafe_reset sign.sign_symbols;
    unsafe_reset sign.sign_deps;
    unsafe_reset sign.sign_builtins;
    unsafe_reset sign.sign_notations;
    let rec reset_term t =
      let reset_binder b = reset_term (snd (Bindlib.unbind b)) in
      match unfold t with
      | Vari(_)     -> ()
      | Type        -> ()
      | Kind        -> ()
      | Symb(s)     -> shallow_reset_sym s
      | Prod(a,b)   -> reset_term a; reset_binder b
      | Abst(a,t)   -> reset_term a; reset_binder t
      | LLet(a,t,u) -> reset_term a; reset_term t; reset_binder u
      | Appl(t,u)   -> reset_term t; reset_term u
      | Meta(_,_)   -> assert false
      | Patt(_,_,m) -> Array.iter reset_term m
      | TEnv(_,m)   -> Array.iter reset_term m
      | Wild        -> ()
      | TRef(r)     -> unsafe_reset r; Option.iter reset_term !r
    and reset_rule r =
      List.iter reset_term r.lhs;
      reset_term (snd (Bindlib.unmbind r.rhs))
    and shallow_reset_sym s =
      unsafe_reset s.sym_type;
      unsafe_reset s.sym_def;
      unsafe_reset s.sym_rules
    in
    let reset_sym s =
      shallow_reset_sym s;
      reset_term !(s.sym_type);
      Option.iter reset_term !(s.sym_def);
      List.iter reset_rule !(s.sym_rules)
    in
    StrMap.iter (fun _ (s,_) -> reset_sym s) !(sign.sign_symbols);
    StrMap.iter (fun _ s -> shallow_reset_sym s) !(sign.sign_builtins);
    SymMap.iter (fun s _ -> shallow_reset_sym s) !(sign.sign_notations);
    let fn (_,r) = reset_rule r in
    PathMap.iter (fun _ -> List.iter fn) !(sign.sign_deps);
    let shallow_reset_inductive i =
      shallow_reset_sym i.ind_prop;
      List.iter shallow_reset_sym i.ind_cons
    in
    let fn s i = shallow_reset_sym s; shallow_reset_inductive i in
    SymMap.iter fn !(sign.sign_ind);
    sign
  in
  reset_timed_refs sign

(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)
