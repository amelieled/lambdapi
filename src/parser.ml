(** Parsing functions for the Lambdapi syntax based on the Pacomb library. See
    https://github.com/craff/pacomb/master/README.md  and  the   documentation
    generated by make  doc for details on using the library and its ppx syntax
    extension. *)

open Extra
open Syntax
open Files
open Pos
open Pacomb

(** {b NOTE} we maintain the invariant that errors reported by the parser have
    a position. To help enforce that, we avoid opening the [Console] module so
    that [Console.fatal] and [Console.fatal_no_pos] are not in scope. To raise
    an error in the parser, only the following function should be used. *)

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces that
    the error has an attached source code position. *)
let parser_fatal : popt -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal loc fmt

(** Currently defined unary operators. *)
let unops : (string, unop) Word_list.t = Word_list.create ()

(** Currently defined binary operators. *)
let binops : (string, binop) Word_list.t = Word_list.create ()

(** Currently defined identifiers. *)
let declared_ids : (string, string) Word_list.t = Word_list.create ()

(** Parser for a declared identifier. *)
let declared_id = Word_list.utf8_word declared_ids

(** The following should not appear as substrings of binary operators, as they
    would introduce ambiguity in the parsing. *)
let forbidden_in_ops =
  [ "("; ")"; "."; "λ"; "∀"; "&"; "["; "]"; "{"; "}"; "?"; ":"; "→"; "⇒"
  ; "@"; ","; ";"; "\""; "\'"; "≔"; "//"; " "; "\r"; "\n"; "\t"; "\b" ]
  @ List.init 10 string_of_int

(** [get_ops loc p] loads the unary and binary operators associated to  module
    [p] and report possible errors at location [loc].  This operation requires
    the module [p] to be loaded (i.e., compiled). The declared identifiers are
    also retrieved at the same time. *)
let get_ops : pos -> p_module_path -> unit = fun loc p ->
  let p = List.map fst p in
  let sign =
    try PathMap.find p Timed.(!(Sign.loaded)) with Not_found ->
      parser_fatal (ByPos loc)
        "Module [%a] not loaded (used for binops)." pp_path p
  in
  let fn s (_, unop) = Word_list.add_utf8 unops s unop in
  StrMap.iter fn Timed.(!Sign.(sign.sign_unops));
  let fn s (_, binop) = Word_list.add_utf8 binops s binop in
  StrMap.iter fn Timed.(!Sign.(sign.sign_binops));
  let fn s = Word_list.add_utf8 declared_ids s s in
  StrSet.iter fn Timed.(!Sign.(sign.sign_idents))

(** Blank function (for comments and white spaces). *)
let blank = Blank.line_comments "//"

(** Set of identifier characters. *)
let id_charset = Charset.from_string "a-zA-Z0-9_'"

(** Keyword module. *)
module KW = Keywords.Make(
  struct
    let id_charset = id_charset
    let reserved = []
  end)

(** Reserve ["KIND"] to disallow it as an identifier. *)
let _ = KW.reserve "KIND"

(** Keyword declarations. Keep alphabetical order. *)
let _abort_      = KW.create "abort"
let _admit_      = KW.create "admit"
let _and_        = KW.create "and"
let _apply_      = KW.create "apply"
let _as_         = KW.create "as"
let _assert_     = KW.create "assert"
let _assertnot_  = KW.create "assertnot"
let _compute_    = KW.create "compute"
let _constant_   = KW.create "constant"
let _definition_ = KW.create "definition"
let _focus_      = KW.create "focus"
let _in_         = KW.create "in"
let _injective_  = KW.create "injective"
let _intro_      = KW.create "assume"
let _let_        = KW.create "let"
let _open_       = KW.create "open"
let _print_      = KW.create "print"
let _private_    = KW.create "private"
let _proof_      = KW.create "proof"
let _proofterm_  = KW.create "proofterm"
let _protected_  = KW.create "protected"
let _qed_        = KW.create "qed"
let _refine_     = KW.create "refine"
let _refl_       = KW.create "reflexivity"
let _require_    = KW.create "require"
let _rewrite_    = KW.create "rewrite"
let _rule_       = KW.create "rule"
let _set_        = KW.create "set"
let _simpl_      = KW.create "simpl"
let _sym_        = KW.create "symmetry"
let _symbol_     = KW.create "symbol"
let _theorem_    = KW.create "theorem"
let _type_       = KW.create "type"
let _TYPE_       = KW.create "TYPE"
let _why3_       = KW.create "why3"
let _wild_       = KW.create "_"

(** [sanity_check pos s] checks that the token [s] is appropriate for an infix
    operator or a declared identifier. If it is not the case, then the [Fatal]
    exception is raised. *)
let sanity_check : pos -> string -> unit = fun loc s ->
  let loc = ByPos loc in
  (* Of course, the empty string and keywords are forbidden. *)
  if s = "" then parser_fatal loc "Invalid token (empty).";
  if KW.mem s then parser_fatal loc "Invalid token (reserved).";
  (* We forbid valid (non-escaped) identifiers. *)
  if String.for_all (Charset.mem id_charset) s then
    parser_fatal loc "Invalid token (only identifier characters).";
  (* We also reject symbols with certain substrings. *)
  let check_substring w =
    if String.is_substring w s then
      parser_fatal loc "Invalid token (has [%s] as a substring)." w
  in
  List.iter check_substring forbidden_in_ops

(** Sequence of alphabetical characters. *)
let alpha : string Grammar.t =
  let alpha = Charset.from_string "a-zA-Z" in
  let fn s0 n0 =
    let rec fn l s n =
      let (c,s',n') = Input.read s n in
      if Charset.mem alpha c then
        fn (l+1) s' n'
      else
        if (l>0) then (Input.sub s0 n0 l, s,n) else Lex.give_up ()
    in
    fn 0 s0 n0
  in
  Grammar.term { n = "<alpha>" ; c = alpha ; f = fn ; a = Lex.custom fn }

(** Regular identifier (regexp ["[a-zA-Z_][a-zA-Z0-9_']*"]). *)
let regular_ident : string Grammar.t =
  let head_cs = Charset.from_string "a-zA-Z_" in
  let body_cs = Charset.from_string "a-zA-Z0-9_'" in
  let fn s0 n0 =
    let rec fn l s n =
      let (c,s',n') = Input.read s n in
      if Charset.mem body_cs c then
        fn (l+1) s' n'
      else
        (Input.sub s0 n0 l, s,n)
    in
    let gn s n =
      let (c,s',n') = Input.read s n in
      if Charset.mem head_cs c then fn 1 s' n'
      else Lex.give_up ()
    in
    gn s0 n0
  in
  Grammar.term { n = "<r-ident>" ; c = head_cs ; f = fn ; a = Lex.custom fn }

(** [escaped_ident with_delim] is a parser for a single escaped identifier. An
    escaped identifier corresponds to an arbitrary sequence of characters that
    starts with ["{|"], ends with ["|}"], and does not contain ["|}"]. Or said
    otherwise, they are recognised by regexp ["{|\([^|]\|\(|[^}]\)\)|*|}"]. If
    [with_delim] is [true] then the returned string includes both the starting
    and the ending delimitors. They are otherwise omited. *)
let escaped_ident : bool -> string Grammar.t = fun with_delim ->
  let fn buf pos =
    let s = Buffer.create 20 in
    (* Check start marker. *)
    let (c, buf, pos) = Input.read buf pos in
    if c <> '{' then Lex.give_up ();
    let (c, buf, pos) = Input.read buf pos in
    if c <> '|' then Lex.give_up ();
    if with_delim then Buffer.add_string s "{|";
    (* Accumulate until end marker. *)
    let rec work buf pos =
      let (c, buf, pos) = Input.read buf pos in
      let (next_c,buf',pos') = Input.read buf pos in
      if c = '|' && next_c = '}' then (buf', pos')
      else if c <> '\255' then (Buffer.add_char s c; work buf pos)
      else Lex.give_up ()
    in
    let (buf, pos) = work buf pos in
    if with_delim then Buffer.add_string s "|}";
    (* Return the contents. *)
    (Buffer.contents s, buf, pos)
  in
  let p_name = if with_delim then "{|<e-ident>|}" else "<e-ident>" in
  Grammar.term { n = p_name ; f = fn
               ; c = Charset.singleton '{'
               ; a = Lex.custom fn }

let escaped_ident_no_delim = escaped_ident false
let escaped_ident = escaped_ident true

(** Any identifier (regular or escaped). *)
let%parser any_ident =
    (id::regular_ident) => (KW.check id; id)
  ; (id::escaped_ident) => id
  ; (id::declared_id)   => id

let%parser reg_or_esc_ident =
    (id::regular_ident) => id (* no check *)
  ; (id::escaped_ident) => id

(** Identifier (regular and non-keyword, or escaped). *)
let%parser ident = (id::any_ident) => in_pos _pos id

let%parser arg_ident =
    (id::ident) => Some(id)
  ; (_wild_)    => None


(** Metavariable identifier (regular or escaped, prefixed with ['?']). *)
let%parser [@layout Blank.none] meta =
  "?" (id::reg_or_esc_ident) =>
    begin
      if id = "_" then Lex.give_up (); in_pos _pos id
    end

(** Pattern variable identifier (regular or escaped, prefixed with ['&']). *)
let%parser [@layout Blank.none] patt =
  "&" (id::reg_or_esc_ident) =>
    begin
      if id = "_" then None else Some(in_pos _pos id)
    end

(** Any path member identifier (escaped idents are stripped). *)
let%parser path_elem =
    (id::regular_ident)          => (KW.check id; (id, false))
  ; (id::escaped_ident_no_delim) => (id, true)

(** Needed to force reading of full path otherwise, might get
    file not found *)
let no_dot g =
  Grammar.test_after
    (fun _ _ _ s n -> let (c,_,_) = Input.read s n in  c <> '.')
    g

(** Module path (dot-separated identifiers. *)
let%parser path = (ms:: ~+ ["."] path_elem) => ms

let path = no_dot path

(** [qident] parses a single (possibly qualified) identifier. *)
let%parser path_prefix =
  (mp:: ~* ((p::path_elem) "." => p)) => mp

let%parser qident =
  (mp::path_prefix) (id::any_ident) => in_pos _pos (mp,id)

let qident = no_dot qident

(** [symtag] parses a single symbol tag. *)
let%parser property =
    _constant_  => Terms.Const
  ; _injective_ => Terms.Injec

(** [exposition] parses the exposition tag of a symbol.*)
let%parser exposition =
    _protected_ => Terms.Protec
  ; _private_   => Terms.Privat

(** Priority level for an expression (term or type). *)
type prio = PAtom | PAppl | POper of float | PFunc

let string_of_prio = function
  | PAtom   -> "A"
  | PAppl   -> "@"
  | POper f -> "B" ^ string_of_float f
  | PFunc   -> "F"

(** [term] is a parser for a term. *)
let%parser [@print_param string_of_prio] rec term (p : prio) =
  (* priorities inheritance *)
    PAtom < PAppl
  ; (p =| POper __) (t::term PAppl)  => t
  ; POper min_float < PFunc
  (* TYPE constant. *)
  ; (p=PAtom) _TYPE_
      => in_pos _pos P_Type
  (* Variable (or possibly explicitly applied and qualified symbol). *)
  ; (p=PAtom) (expl:: ~? [false] ("@" => true)) (qid::qident)
      => in_pos _pos (P_Iden(qid, expl))
  (* Wildcard. *)
  ; (p=PAtom) _wild_
      => in_pos _pos P_Wild
  (* Metavariable. *)
  ; (p=PAtom) (m::meta) (e::env)
      => in_pos _pos (P_Meta(m, Array.of_list e))
  (* Pattern (LHS) or pattern application (RHS). *)
  ; (p=PAtom) (p::patt) (e::env)
      => in_pos _pos (P_Patt(p, Array.of_list e))
  (* Parentheses. *)
  ; (p=PAtom) "(" (t::term PFunc) ")"
      => in_pos _pos (P_Wrap(t))
  (* Explicitly given argument. *)
  ; (p=PAtom) "{" (t::term PFunc) "}"
      => in_pos _pos (P_Expl(t))
  (* Application. *)
  ; (p=PAppl) (t::term PAppl) (u::term PAtom)
      => in_pos _pos (P_Appl(t,u))
  (* Implication. *)
  ; (p=PFunc) (a::term (POper min_float)) "⇒" (b::term PFunc)
      => in_pos _pos (P_Impl(a,b))
  (* Products. *)
  ; (p=PFunc) "∀" (xs:: ~+ arg) "," (b::term PFunc)
      => in_pos _pos (P_Prod(xs,b))
  ; (p=PFunc) "∀" (xs:: ~+ arg_ident) ":" (a::term PFunc) "," (b::term PFunc)
      => in_pos _pos (P_Prod([xs,Some(a),false],b))
  (* Abstraction. *)
  ; (p=PFunc) "λ" (xs:: ~+ arg) "," (t::term PFunc)
      => in_pos _pos (P_Abst(xs,t))
  ; (p=PFunc) "λ" (xs:: ~+ arg_ident) ":" (a::term PFunc) "," (t::term PFunc)
      => in_pos _pos (P_Abst([xs,Some(a),false],t))
  (* Local let. *)
  ; (p=PFunc) _let_ (x::ident) (a:: ~* arg) "≔" (t::term PFunc)
         _in_ (u::term PFunc)
      => in_pos _pos (P_LLet(x,a,t,u))
  (* Natural number literal. *)
  ; (p=PAtom) (n::NAT)
      => in_pos _pos (P_NLit(n))
  (* Unary operator. *)
  ; (p=|POper q) ((q,u)>:unop q) (t::term (POper q)) =>
      in_pos _pos (P_UnaO(u,t))
  (* Binary operator. *)
  ; (p=|POper q) ((pt,t)>:pBinO q) ((q,b)>:binop pt q) ((__,u)::pBinO q) =>
      in_pos _pos (P_BinO(t,b,u))

(** parser collecting the priority, used left of an infix *)
and pBinO q =
  (t::term (POper q)) =>
    begin
      let p =
        match t.elt with
        | P_BinO(_,(_,_,p,_),_) -> p
        | _                     -> max_float
      in
      (p, t)
    end

(** Parser for a binary operator. receive the priority of the left term and
   return the priority for the right term *)
and binop pmax pmin =
  (((__, assoc, p, ___) = b)::Word_list.utf8_word binops) =>
    begin
      (* Find out minimum priorities for left and right operands. *)
      let (good, p) =
        let p_plus_epsilon = p +. 1e-6 in
        match assoc with
        | Assoc_none  -> (pmin <=  p && p <  pmax, p)
        | Assoc_right -> (pmin <=  p && p <  pmax, p)
        | Assoc_left  -> (pmin <=  p && p <= pmax, p_plus_epsilon)
      in
      (* Check that priority of left operand is above [min_pl]. *)
      if not good then Lex.give_up ();
      (p,b)
    end

and unop pmin =
  (((__, p, ___) = b)::Word_list.utf8_word unops) =>
    begin
      if p < pmin then Lex.give_up ();
      (p,b)
    end

(*
(* NOTE on binary operators. To handle infix binary operators, we need to rely
   on a dependent (Pacomb) grammar. The operands are parsed using the priority
   level [POper]. The left operand is parsed first, together with the operator
   to obtain the corresponding priority and associativity parameters.  We then
   check whether the (binary operator) priority level [pl] of the left operand
   satifies the conditions, and reject it early if it does not.  We then parse
   the right operand in a second step, and also check whether it satisfies the
   required condition before accepting the parse tree. *)

(** [env] is a parser for a metavariable environment. *)
   *)
and env =
    ()                                 => []
  ; "[" (ts:: ~+ [","] (term (POper min_float))) "]" => ts

(** [arg] parses a single function argument. *)
and arg =
  (* Explicit argument without type annotation. *)
    (x::arg_ident)                                  => ([x], None,    false)
  (* Explicit argument with type annotation. *)
  ; "(" (xs:: ~+ arg_ident) ":" (a::term PFunc) ")" => (xs , Some(a), false)
  (* Implicit argument (with possible type annotation). *)
  ; "{" (xs:: ~+ arg_ident) (a:: ~? (":" (t::term PFunc) => t)) "}"
                                                    => (xs , a      , true )
let term = term PFunc

(** [rule] is a parser for a single rewriting rule. *)
let%parser rule =
  (l::term) "→" (r::term) => in_pos _pos (l, r)

(** [rw_patt_spec] is a parser for a rewrite pattern specification. *)
let%parser rw_patt_spec =
    (t::term)                                => P_rw_Term(t)
  ; _in_ (t::term)                           => P_rw_InTerm(t)
  ; _in_ (x::ident) _in_ (t::term)           => P_rw_InIdInTerm(x,t)
  ; (x::ident) _in_ (t::term)                => P_rw_IdInTerm(x,t)
  ; (u::term) _in_ (x::ident) _in_ (t::term) => P_rw_TermInIdInTerm(u,x,t)
  ; (u::term) _as_ (x::ident) _in_ (t::term) => P_rw_TermAsIdInTerm(u,x,t)

(** [rw_patt] is a parser for a (located) rewrite pattern. *)
let%parser rw_patt = "[" (r::rw_patt_spec) "]" => in_pos _pos r

let%parser assert_must_fail =
    _assert_    => false
  ; _assertnot_ => true

(** [assertion] parses a single assertion. *)
let%parser assertion =
    (t::term) ":" (a::term) => P_assert_typing(t,a)
  ; (t::term) "≡" (u::term) => P_assert_conv(t,u)
  (* FIXME potential conflict with infix "≡". *)

let%parser sign : bool Grammar.t =
  Grammar.no_blank_after ('+' => true ; '-' => false)

(** [query] parses a query. *)
let%parser query : p_query Grammar.t =
    _set_ "verbose" (i::NAT) =>
      in_pos _pos (P_query_verbose(i))
  ; _set_ "debug" (b::sign) (s::alpha) =>
      in_pos _pos (P_query_debug(b, s))
  ; _set_ "flag" (s::STRING_LIT) (b::("on" => true ; "off" => false)) =>
      in_pos _pos (P_query_flag(s, b))
  ; (mf::assert_must_fail) (a::assertion) =>
      in_pos _pos (P_query_assert(mf,a))
  ; _type_ (t::term) => (
      let c = Eval.{strategy = NONE; steps = None} in
      in_pos _pos (P_query_infer(t,c)))
  ; _compute_ (t::term) => (
      let c = Eval.{strategy = SNF; steps = None} in
      in_pos _pos (P_query_normalize(t,c)))
  ; _set_ "prover" (s::STRING_LIT) =>
      in_pos _pos (P_query_prover(s))
  ; _set_ "prover_timeout" (n::NAT) =>
      in_pos _pos (P_query_prover_timeout(n))

(** [tactic] is a parser for a single tactic. *)
let%parser tactic =
    _refine_ (t::term)                => in_pos _pos (P_tac_refine(t))
  ; _intro_ (xs:: ~+ arg_ident)       => in_pos _pos (P_tac_intro(xs))
  ; _apply_ (t::term)                 => in_pos _pos (P_tac_apply(t))
  ; _simpl_                           => in_pos _pos P_tac_simpl
  ; _rewrite_ (p:: ~? rw_patt) (t::term)
                                      => in_pos _pos (P_tac_rewrite(p,t))
  ; _refl_                            => in_pos _pos P_tac_refl
  ; _sym_                             => in_pos _pos P_tac_sym
  ; _focus_ (i::NAT)                  => in_pos _pos (P_tac_focus(i))
  ; _print_                           => in_pos _pos P_tac_print
  ; _proofterm_                       => in_pos _pos P_tac_proofterm
  ; _why3_ (s:: ~? STRING_LIT)        => in_pos _pos (P_tac_why3(s))
  ; (q::query)                        => in_pos _pos (P_tac_query(q))

(** [proof_end] is a parser for a proof terminator. *)
let%parser proof_end =
    _qed_   => P_proof_qed
  ; _admit_ => P_proof_admit
  ; _abort_ => P_proof_abort

let%parser assoc =
   ()       => Assoc_none
  ; "left"  => Assoc_left
  ; "right" => Assoc_right

(** [config] parses a single configuration option. *)
let%parser [@cache] config =
    "builtin" (s::STRING_LIT) "≔" (qid::qident) =>
      P_config_builtin(s,qid)
  ; "prefix" (p::FLOAT) (s::STRING_LIT) "≔" (qid::qident) =>
      begin
        let unop = (s, p, qid) in
        sanity_check s_pos s;
        Word_list.add_utf8 unops s unop;
        P_config_unop(unop)
      end
  ; "infix" (a::assoc) (p::FLOAT) (s::STRING_LIT) "≔" (qid::qident) =>
      begin
        let binop = (s, a, p, qid) in
        sanity_check s_pos s;
        Word_list.add_utf8 binops s binop;
        P_config_binop(binop)
      end
  ; "declared" (id::STRING_LIT) =>
      begin
        sanity_check id_pos id;
        Word_list.add_utf8 declared_ids id id;
        P_config_ident(id)
      end

let%parser statement =
  _theorem_ (s::ident) (al:: ~* arg) ":" (a::term) _proof_
    => in_pos _pos (s,al,a)

let%parser proof =
  (ts:: ~*tactic) (e::proof_end) => (ts, in_pos e_pos e)

(** [!require mp] can be used to require the compilation of a module [mp] when
    it is required as a dependency. This has the effect of importing notations
    exported by that module. The value of [require] is set in [Compile], and a
    reference is used to avoid to avoid cyclic dependencies. *)
let require : (Files.module_path -> unit) Stdlib.ref = ref (fun _ -> ())

(** [do_require pos path] is a wrapper for [!require path], that takes care of
    possible exceptions. Errors are reported at given position [pos],  keeping
    as much information as possible in the error message. *)
let do_require : popt -> p_module_path -> unit = fun loc path ->
  let path = List.map fst path in
  let local_fatal fmt =
    let fmt = "Error when loading module [%a].\n" ^^ fmt in
    parser_fatal loc fmt Files.pp_path path
  in
  (* We attach our position to errors comming from the outside. *)
  try !require path with
  | Console.Fatal(None     , msg) -> local_fatal "%s" msg
  | Console.Fatal(Some(pos), msg) -> local_fatal "[%a] %s" print pos msg
  | e                             -> local_fatal "Uncaught exception: [%s]"
                                       (Printexc.to_string e)

(** [cmd] is a parser for a single command. *)
let%parser cmd =
    _require_ (o:: ~? [false] (_open_ => true)) (ps:: ~+ path)
      => begin
        let fn p = do_require (ByPos _pos) p; if o then get_ops _pos p in
        List.iter fn ps; P_require(o,ps)
      end
  ; _require_ (p::path) _as_ (n::path_elem)
      => begin
        do_require (ByPos _pos) p;
        P_require_as(p, in_pos n_pos n)
      end
  ; _open_ (ps:: ~+path)
      => begin
        List.iter (get_ops _pos) ps;
        P_open(ps)
      end
  ; (e:: ~?exposition) (p:: ~? property) _symbol_
      (s::ident) (al:: ~*arg) ":" (a::term)
      => P_symbol(Option.get Terms.Public e,Option.get Terms.Defin p,s,al,a)
  ; _rule_ (rs:: ~+ [_and_] rule)
      => P_rules(rs)
  ; (e:: ~?exposition) _definition_
      (s::ident) (al:: ~*arg) (ao:: ~? (":" (t::term) => t)) "≔" (t::term)
      => P_definition(Option.get Terms.Public e,false,s,al,ao,t)
  ; (e:: ~? exposition) (st::statement) ((ts,pe)::proof)
      => P_theorem(Option.get Terms.Public e,st,ts,pe)
  ; _set_ (c::config)
      => P_set(c)
  ; (q::query)
      => P_query(q)

(** [cmds] is a parser for multiple (located) commands. It "folds" on the
   commands uusing the given accumalator and function rather that return a
   list *)
let cmds : type a. a -> (a -> p_command -> a) -> a Grammar.t = fun acc fn ->
  (* lazy is necessary  otherwise  command which are prefix of another command
     are evaluated,  and as this  may  modify  some  global  state,  this is a
     catastrophy. The lazy trick below evaluates a command only after the next
     command of EOF have been parsed. *)
  let%parser rec cmds =
    ()                     => lazy acc
    ; (acc::cmds) (c::cmd) => let acc = Lazy.force acc in
                              lazy (fn acc (in_pos c_pos c))
  in
  let%parser top = (acc::cmds) EOF => Lazy.force acc in
  top

let reset_ops () =
  let open Word_list in
  let u = save_and_reset unops in
  let b = save_and_reset binops in
  let d = save_and_reset declared_ids in
  (u, b, d)

let restore_ops (u,b,d) =
  let open Word_list in
  restore unops u; restore binops b; restore declared_ids d

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is given through the [Fatal] exception. *)
let parse_file : string -> 'a fold = fun fname acc fn ->
  let saved = reset_ops () in
  try
    let r =
      Grammar.parse_file ~utf8:UTF8 (cmds acc fn) blank fname in
    restore_ops saved; r
  with Pos.Parse_error(buf,pos,_msgs) ->
    restore_ops saved;
    let (infos,p) = Input.spos buf pos in
    let pos = mk_pos p p infos in
    parser_fatal (ByPos pos) "Parse error."

(** [parse_string fname str] attempts to parse the string [str] file to obtain
    a list of toplevel commands.  In case of failure, a graceful error message
    containing the error position is given through the [Fatal] exception.  The
    [fname] argument should contain a relevant file name for the error message
    to be constructed. *)
let parse_string : string -> string -> 'a fold = fun _fname str acc fn ->
  let saved = reset_ops () in
  try
    let r =
      Grammar.parse_string ~utf8:UTF8 (cmds acc fn) blank str
    in
    restore_ops saved; r
  with Pos.Parse_error(buf,pos,_msgs) ->
    restore_ops saved;
    let (infos,p) = Input.spos buf pos in
    let pos = mk_pos p p infos in
    parser_fatal (ByPos pos) "Parse error."
