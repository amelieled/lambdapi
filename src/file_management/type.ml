
open Lplib.Base
open Pos

(** Representation of a (located) identifier. *)
type ident = strloc

(** Parsing representation of a module path. For every path member the boolean
    indicates whether it was given using the escaped syntax. *)
type p_module_path = (string * bool) list

(** Representation of a possibly qualified (and located) identifier. *)
type qident_aux = p_module_path * string
type qident = qident_aux loc

(** The priority of an infix operator is a floating-point number. *)
type priority = float

(** Representation of a unary operator. *)
type unop = string * priority * qident

(** Representation of a binary operator. *)
type binop = string * Pratter.associativity * priority * qident

module Tags = struct
  (** Pattern-matching strategy modifiers. *)
  type match_strat =
    | Sequen
    (** Rules are processed sequentially: a rule can be applied only if the
        previous ones (in the order of declaration) cannot be. *)
    | Eager
    (** Any rule that filters a term can be applied (even if a rule defined
        earlier filters the term as well). This is the default. *)

  (** Specify the visibility and usability of symbols outside their module. *)
  type expo =
    | Public
    (** Visible and usable everywhere. *)
    | Protec
    (** Visible everywhere but usable in LHS arguments only. *)
    | Privat
    (** Not visible and thus not usable. *)

  (** Symbol properties. *)
  type prop =
    | Defin
    (** The symbol is definable by rewriting rules. *)
    | Const
    (** The symbol cannot be defined. *)
    | Injec
    (** The symbol is definable but is assumed to be injective. *)

  let pp_prop : prop pp = fun oc p ->
    match p with
    | Defin -> ()
    | Const -> Format.fprintf oc "constant "
    | Injec -> Format.fprintf oc "injective "

  let pp_expo : expo pp = fun oc e ->
    match e with
    | Public -> ()
    | Protec -> Format.fprintf oc "protected "
    | Privat -> Format.fprintf oc "private "

  let pp_match_strat : match_strat pp = fun oc s ->
    match s with
    | Sequen -> Format.fprintf oc "sequential "
    | Eager -> ()
end

type ('term, 'binder) rw_patt_aux =
  | RW_Term           of 'term
  | RW_InTerm         of 'term
  | RW_InIdInTerm     of 'binder
  | RW_IdInTerm       of 'binder
  | RW_TermInIdInTerm of 'term * 'binder
  | RW_TermAsIdInTerm of 'term * 'binder

(* Then, p_rw_patt = (p_term, p_ident * p_term) rw_patt_aux loc
and rw_patt = (term, tbinder) rw_patt_aux loc *)

                       
(** Type representing the different evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

(** Configuration for evaluation. *)
type eval_config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }
