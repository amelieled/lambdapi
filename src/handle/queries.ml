(** Queries (available in tactics and at the toplevel). *)

open File_management.Error
open File_management.Pos
open File_management.Type.Tags
open Parsing.Syntax
open Data_structure.Terms (* empty_problem only! *)
open! Type_checking
open Rewriting_engine.Print
open! Rewriting_engine
open Proof_mode.Proof (* proof_state option only! *)
open! Lplib

open Scoping
open Data_structure

open Csig_state_find_sym
   
(** Result of query displayed on hover in the editor*)
type result = string option

(** [handle_query ss ps q] *)
let handle_query : Sig_state.t -> proof_state option -> p_query -> result =
  fun ss ps q ->
  match q.elt with
  | P_query_assert(must_fail, asrt) ->
      let env = Proof_mode.Proof.focus_env ps in
      let ctxt = Env.to_ctxt env in
      let scope = Scope.scope_term Public ss env in
      begin
      match asrt with
      | P_assert_typing(pt,pa) ->
          let t = scope pt and a = scope pa in
          out 1 "(asrt) it is %b that %a\n" (not must_fail)
            pp_typing (ctxt, t, a);
          (* Check that [a] is typable by a sort. *)
          Infer.check_sort Unif.solve_noexn q.pos ctxt a;
          let result =
            try Infer.check Unif.solve_noexn q.pos ctxt t a; true
            with Fatal _ -> false
          in if result = must_fail then fatal q.pos "Assertion failed."
      | P_assert_conv(pt,pu) ->
          let t = scope pt and u = scope pu in
          out 1 "(asrt) it is %b that %a\n" (not must_fail)
            pp_constr (ctxt, t, u);
          (* Check that [t] is typable. *)
          let a = Infer.infer Unif.solve_noexn pt.pos ctxt t in
          (* Check that [u] is typable. *)
          let b = Infer.infer Unif.solve_noexn pu.pos ctxt u in
          (* Check that [t] and [u] have the same type. *)
          let to_solve = [ctxt,a,b] in
          match Unif.(solve_noexn {empty_problem with to_solve}) with
          | None ->
              fatal q.pos "[%a] has type [%a].\n[%a] has type [%a].\n\
                           Those two types are not unifiable."
                pp_term t pp_term a pp_term u pp_term b
          | Some ((_::_) as cs) ->
              List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
              fatal q.pos "[%a] has type [%a]\n[%a] has type [%a]\n\
                           Those two types are not unifiable."
                pp_term t pp_term a pp_term u pp_term b
          | Some [] ->
              if Eval.eq_modulo ctxt t u = must_fail then
                fatal q.pos "Assertion failed."
      end;
      None
  | P_query_infer(pt, cfg) ->
      let env = Proof_mode.Proof.focus_env ps in
      let ctxt = Env.to_ctxt env in
      let scope = Scope.scope_term Public ss env in
      let t = scope pt in
      let a = Infer.infer Unif.solve_noexn pt.pos ctxt t in
      let res = Eval.eval cfg ctxt a in
      out 1 "(infr) %a : %a\n" pp_term t pp_term res;
      Some (Format.asprintf "%a : %a" pp_term t pp_term res)
  | P_query_normalize(pt, cfg) ->
      let env = Proof_mode.Proof.focus_env ps in
      let ctxt = Env.to_ctxt env in
      let scope = Scope.scope_term Public ss env in
      let t = scope pt in
      (* Check that [t] is typable. *)
      ignore (Infer.infer Unif.solve_noexn pt.pos ctxt t);
      out 1 "(comp) %a\n" pp_term (Eval.eval cfg ctxt t);
      Some (Format.asprintf "%a" pp_term (Eval.eval cfg ctxt t))
  | P_query_print(None) ->
      (match ps with
       | None -> fatal q.pos "Not in a proof."
       | Some ps -> out 1 "%a" Proof_mode.Proof.pp_goals ps;
                    Some (Format.asprintf "%a" Proof_mode.Proof.pp_goals ps))
  | P_query_print(Some qid) ->
      let sym = find_sym ~prt:true ~prv:true false ss qid in
      let open Timed in
      out 1 "(prnt) %a%a%asymbol %a: %a" pp_expo sym.sym_expo
        pp_prop sym.sym_prop pp_match_strat !(sym.sym_mstrat)
        pp_symbol sym pp_term !(sym.sym_type);
      Option.iter (fun h -> out 1 " [%a]" notation h) (notation_of sym);
      (match !(sym.sym_def) with
      | Some t ->
          out 1 " ≔ %a\n" pp_term t;
          Some (Format.asprintf " ≔ %a" pp_term t)
      | None ->
          out 1 "\n";
          let rule oc r = Format.fprintf oc "%a\n" pp_rule (sym, r) in
          out 1 "%a" (List.pp rule "") !(sym.sym_rules);
          Some (Format.asprintf "%a" (List.pp rule "") !(sym.sym_rules)))
  | P_query_proofterm ->
      (match ps with
       | None -> fatal q.pos "Not in a proof"
       | Some ps ->
           match ps.proof_term with
           | Some t ->
              out 1 "%a\n" pp_term (Meta(t,[||]));
              Some (Format.asprintf "%a" pp_term (Meta(t,[||])))
           | None -> fatal q.pos "Not in a definition")
