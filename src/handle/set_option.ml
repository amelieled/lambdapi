(** Set option for files *)

open Timed

open File_management.Pos
open File_management.Error

open Proof_mode.Why3_tactic

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled; _} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Stdlib.(!loggers);
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled Stdlib.(!loggers)

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
    default. *)
let set_default_debug : string -> unit = fun str ->
  Stdlib.(default_loggers := str); set_debug true str

(** [set_flag id b] sets the value of the flag named [id] to be [b], or raises
    [Not_found] if no flag with this name was registered. *)
let set_flag : string -> bool -> unit = fun id b ->
  snd (Lplib.Extra.StrMap.find id Stdlib.(!boolean_flags)) := b
   
(** [handle_set_option q] *)
let handle_set_option : Parsing.Syntax.p_set_option -> 'a = fun q ->
  match q.elt with
  | P_set_option_debug(e,s) ->
      (* Just update the option, state not modified. *)
      set_debug e s; out 3 "(flag) debug → %s%s\n" (if e then "+" else "-") s;
  | P_set_option_verbose(i) ->
      (* Just update the option, state not modified. *)
      if Timed.(!verbose) = 0 then
        (Timed.(verbose := i); out 1 "(flag) verbose → %i\n" i)
      else
        (out 1 "(flag) verbose → %i\n" i; Timed.(verbose := i));
  | P_set_option_flag(id,b) ->
      (* We set the value of the flag, if it exists. *)
      (try set_flag id b
       with Not_found -> wrn q.pos "Unknown flag \"%s\"." id);
      out 3 "(flag) %s → %b\n" id b;
  | P_set_option_prover(s) ->
      Timed.(default_prover := s);
  | P_set_option_prover_timeout(n) ->
      Timed.(timeout := n);
