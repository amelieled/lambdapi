(** Signature for symbols. *)

open! Lplib
open Lplib.Extra

(*open! Parsing*)
   
open Timed
open File_management.Error
open File_management.Module
open Terms
(*open Parsing.Syntax*)
open File_management.Pos
open File_management.Type
open Tags

(** Representation of an inductive type *)
type inductive =
  { ind_cons  : sym list  (** List of constructors                 *)
  ; ind_prop  : sym       (** Induction principle on propositions. *) }

(** Notation properties of symbols. They are linked to symbols to provide
    syntax extensions to these symbols. These syntax extensions concern both
    parsing and printing. *)
type notation =
  | Prefix of unop (** Prefix (or unary) operator, such as [!] in [! x]. *)
  | Infix of binop (** Infix (or binary) operator, such as [+] in [a + b]. *)
  | Zero (** The numeral zero, that is [0]. *)
  | Succ (** Successor, for numerals such as [42]. *)
  | Quant (** Quantifier, such as [fa] in [`fa x, t]. *)

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * File_management.Pos.popt) StrMap.t ref
  ; sign_path     : Path.t
  ; sign_deps     : (string * rule) list PathMap.t ref
  ; sign_builtins : sym StrMap.t ref
  ; sign_notations: notation SymMap.t ref
    (** Maps symbols to their syntax properties if they have some. *)
  ; sign_ind      : inductive SymMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   external modules on which the current signature depends to an association
   list. This association list then maps definable symbols of the external
   module to additional reduction rules defined in the current signature. *)

(** The empty signature. It's a thunk to force the creation of a new record on
    each call (and avoid unwanted sharing). *)
let dummy : unit -> t = fun () ->
  { sign_symbols = ref StrMap.empty; sign_path = []
  ; sign_deps = ref PathMap.empty; sign_builtins = ref StrMap.empty
  ; sign_notations = ref SymMap.empty; sign_ind = ref SymMap.empty }

(** [create sign_path] creates an empty signature with module path
    [sign_path]. *)
let create : Path.t -> t = fun sign_path ->
  let d = dummy () in { d with sign_path }

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym =
  fun sign name -> fst (StrMap.find name !(sign.sign_symbols))

(** [mem sign name] checks whether a symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool =
  fun sign name -> StrMap.mem name !(sign.sign_symbols)

(** [loaded] stores the signatures of the known (already compiled or currently
    being compiled) modules. An important invariant is that all occurrences of
    a symbol are physically equal, even across signatures). This is ensured by
    making copies of terms when loading an object file. *)
let loaded : t PathMap.t ref = ref PathMap.empty

(* NOTE that the current module is stored in [loaded] so that the symbols that
   it contains can be qualified with the name of the module. This behavior was
   inherited from previous versions of Dedukti. *)

(** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)
let loading : Path.t list ref = ref []

(** [current_sign ()] returns the current signature. *)
let current_sign () =
  let mp =
    match !loading with
    | mp :: _ -> mp
    | []      -> assert false
  in
  PathMap.find mp !loaded

(** [path] and [ghost_sign] provide a signature to be used to handle 
    unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

(** Path of the module. *)
let path = Path.ghost "unif_rule"

(** Ghost signature holding the symbols used in unification rules.
    - All signatures depend on it (dependency set in
      {!val:Sig_state.create_sign}).
    - All signatures open it (opened in {!val:Sig_state.of_sign}).
    - It is automatically loaded. *)
let ghost_sign : t =
  let dummy = dummy () in
  let s = {dummy with sign_path = path} in
  loaded := File_management.Module.PathMap.add path s !loaded; s

(** [create_sym e p name type blist] creates a new symbol
    with the exposition [e], the property [p], the name [name]
    the type [type] and no implicit arguments *)
let create_sym : expo -> prop -> string -> term -> bool list -> sym =
  fun e p name typ blist ->
  let path = (current_sign()).sign_path in
  { sym_name = name ; sym_type = ref typ ; sym_path = path
    ; sym_def = ref None ; sym_impl = blist; sym_rules = ref []
    ; sym_prop = p ; sym_expo = e ; sym_tree = ref Tree_types.empty_dtree
    ; sym_mstrat = ref Eager }

(** [add_symbol sign expo prop mstrat name a impl] creates a fresh symbol with
    name [name], exposition [expo], property [prop], matching strategy
    [strat], type [a] and implicit arguments [impl] in the signature [sign].
    [name] should not already be used in [sign]. The created symbol is
    returned. *)
let add_symbol : t -> expo -> prop -> match_strat -> strloc -> term ->
  bool list -> sym = fun sign sym_expo sym_prop sym_mstrat s a impl ->
  (* Check for metavariables in the symbol type. *)
  if Basics.has_metas true a then
    fatal s.pos "The type of [%s] contains metavariables" s.elt;
  (* We minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  let sym_impl = List.rev (rem_false (List.rev impl)) in
  (* Add the symbol. *)
  let sym =
    { sym_name = s.elt; sym_type = ref (cleanup a); sym_path = sign.sign_path
    ; sym_def = ref None; sym_impl; sym_rules = ref []; sym_prop
    ; sym_expo ; sym_tree = ref Tree_types.empty_dtree
    ; sym_mstrat = ref sym_mstrat }
  in
  sign.sign_symbols := StrMap.add s.elt (sym, s.pos) !(sign.sign_symbols); sym

(** [add_rule sign sym r] adds the new rule [r] to the symbol [sym].  When the
    rule does not correspond to a symbol of signature [sign],  it is stored in
    its dependencies. *)
let add_rule : t -> sym -> rule -> unit = fun sign sym r ->
  sym.sym_rules := !(sym.sym_rules) @ [r];
  if sym.sym_path <> sign.sign_path then
    let m =
      try PathMap.find sym.sym_path !(sign.sign_deps)
      with Not_found -> assert false
    in
    let m = (sym.sym_name, r) :: m in
    sign.sign_deps := PathMap.add sym.sym_path m !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin name [name] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins);
  match s with
  | "0" -> sign.sign_notations := SymMap.add sym Zero !(sign.sign_notations)
  | "+1" -> sign.sign_notations := SymMap.add sym Succ !(sign.sign_notations)
  | _ -> ()

(** [add_unop sign sym unop] binds the unary operator [unop] to [sym] in
    [sign]. If [unop] was previously bound, the previous binding is
    discarded. *)
let add_unop : t -> sym -> unop -> unit = fun sign sym unop ->
  sign.sign_notations := SymMap.add sym (Prefix unop) !(sign.sign_notations)

(** [add_binop sign sym binop] binds the binary operator [binop] to [sym] in
    [sign]. If [op] was previously bound, the previous binding is
    discarded. *)
let add_binop : t -> sym -> binop -> unit =
  fun sign sym binop ->
  sign.sign_notations := SymMap.add sym (Infix binop) !(sign.sign_notations)

(** [add_quant sign sym] add the quantifier [sym] to [sign]. *)
let add_quant : t -> sym -> unit = fun sign sym ->
  sign.sign_notations := SymMap.add sym Quant !(sign.sign_notations)

(** [add_inductive sign typ ind_cons ind_prop] add the inductive type which
    consists of a type [typ], constructors [ind_cons] and an induction
    principle [ind_prop] to [sign]. *)
let add_inductive : t -> sym -> sym list -> sym -> unit =
  fun sign typ ind_cons ind_prop ->
  let ind = { ind_cons ; ind_prop } in
  sign.sign_ind := SymMap.add typ ind !(sign.sign_ind)
