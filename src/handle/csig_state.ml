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

open Data_structure.Terms
open Data_structure.Sig_state
open Data_structure.Sign
open! Data_structure

(** [update_notations_from_builtins old_bm new_bm notations] generates a new
    pp_hint map from [notations] when adding [new_bm] to the builtin map
    [old_bm]. *)
let update_notations_from_builtins
    : sym StrMap.t -> sym StrMap.t -> notation SymMap.t -> notation SymMap.t =
  fun old_bm new_bm notations ->
  let add_hint name h notations =
    try
      let s_new = StrMap.find name new_bm in
      try
        let s_old = StrMap.find name old_bm in
        SymMap.add s_new h (SymMap.remove s_old notations)
      with Not_found -> SymMap.add s_new h notations
    with Not_found -> notations
  in
  add_hint "0" Zero (add_hint "+1" Succ notations)

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let builtins = StrMap.union f ss.builtins !(sign.sign_builtins) in
  (* Bring operators in scope *)
  let open_synt s syn ssis =
    match syn with
    | Sign.Infix (k,_, _, _) -> StrMap.add k (s, None) ssis
    | Sign.Prefix (k,_,_) -> StrMap.add k (s, None) ssis
    | _ -> ssis
  in
  let in_scope = SymMap.fold open_synt !(sign.sign_notations) in_scope in
  let notations =
    SymMap.fold SymMap.add !(sign.sign_notations) ss.notations
  in
  let notations =
    update_notations_from_builtins ss.builtins !(sign.sign_builtins) notations
  in
  {ss with in_scope; builtins; notations}

(** [of_sign sign] creates a state from the signature [sign] with ghost
    signatures opened. *)
let of_sign : Sign.t -> sig_state = fun signature ->
  open_sign {Sig_state.dummy with signature} Sign.ghost_sign
