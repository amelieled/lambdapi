(** Signature state.

   This module provides a record type [sig_state] containing all the
   informations needed for scoping p_terms and printing terms, and functions
   on this type for manipulating it. In particular, it provides functions
   [open_sign], [add_symbol], [add_binop], etc. taking a [sig_state] as
   argument and returning a new [sig_state] as result. These functions call
   the corresponding functions of [Sign] which should not be called directly
   but through the current module only, in order to setup the [sig_state]
   properly. *)

open Lplib.Extra

open Timed

open File_management.Module
open File_management.Pos
open File_management.Type
open Tags

open Terms
open Sign

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature.        *)
  ; in_scope  : (sym * popt) StrMap.t     (** Symbols in scope.         *)
  ; aliases   : Path.t StrMap.t           (** Established aliases.      *)
  ; path_map  : string PathMap.t          (** Reverse map of [aliases]. *)
  ; builtins  : sym StrMap.t              (** Builtin symbols.          *)
  ; notations : notation SymMap.t         (** Printing hints.           *) }

type t = sig_state

(** Dummy [sig_state] made from the dummy signature. *)
let dummy : sig_state =
  { signature = Sign.dummy (); in_scope = StrMap.empty; aliases = StrMap.empty
  ; path_map = PathMap.empty; builtins = StrMap.empty
  ; notations = SymMap.empty }
  
(** [create_sign path] creates a signature with path [path] with ghost modules
    as dependencies. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  let d = Sign.dummy () in
  { d with sign_path ; sign_deps = ref (PathMap.singleton Sign.path []) }

(** Symbol properties needed for the signature *)
type sig_symbol =
  { expo   : expo        (** exposition          *)
  ; prop   : prop        (** property            *)
  ; mstrat : match_strat (** strategy            *)
  ; ident  : ident       (** name                *)
  ; typ    : term        (** type                *)
  ; impl   : bool list   (** implicit arguments  *)
  ; def    : term option (** optional definition *) }

(** [add_symbol ss sig_symbol={e,p,st,x,a,impl,def}] generates a new signature
   state from [ss] by creating a new symbol with expo [e], property [p],
   strategy [st], name [x], type [a], implicit arguments [impl] and optional
   definition [t]. This new symbol is returned too. *)
let add_symbol : sig_state -> sig_symbol -> sig_state * sym =
  fun ss {expo=e;prop=p;mstrat=st;ident=x;typ=a;impl;def=t} ->
  let s = Sign.add_symbol ss.signature e p st x a impl in
  begin
    match t with
    | Some t -> s.sym_def := Some (cleanup t)
    | None -> ()
  end;
  let in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope in
  ({ss with in_scope}, s)

(** [add_unop ss n x] generates a new signature state from [ss] by adding a
    unary operator [x] with name [n]. This name is added to the scope. *)
let add_unop : sig_state -> strloc -> (sym * unop) -> sig_state =
  fun ss name (sym, unop) ->
  Sign.add_unop ss.signature sym unop;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let notations = SymMap.add sym (Prefix unop) ss.notations in
  {ss with in_scope; notations}

(** [add_binop ss n x] generates a new signature state from [ss] by adding a
    binary operator [x] with name [n]. This name is added to scope. *)
let add_binop : sig_state -> strloc -> (sym * binop) -> sig_state =
  fun ss name (sym, binop) ->
  Sign.add_binop ss.signature sym binop;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let notations = SymMap.add sym (Infix binop) ss.notations in
  {ss with in_scope; notations}

(** [add_builtin ss n s] generates a new signature state from [ss] by mapping
   the builtin [n] to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state = fun ss name sym ->
  Sign.add_builtin ss.signature name sym;
  let builtins = StrMap.add name sym ss.builtins in
  let add_pp_hint hint = SymMap.add sym hint ss.notations in
  let notations =
    match name with
    | "0"  -> add_pp_hint Zero
    | "+1" -> add_pp_hint Succ
    | _    -> ss.notations
  in
  {ss with builtins; notations}

(** [add_quant ss sym] generates a new signature state from [ss] by declaring
   [sym] as quantifier. *)
let add_quant : sig_state -> sym -> sig_state = fun ss sym ->
  Sign.add_quant ss.signature sym;
  {ss with notations = SymMap.add sym Quant ss.notations}
