

open Timed
open Lplib.Extra

open File_management.Error



(** Module to manipulate imperative state of the typechecker. *)
module State = struct
  (** Settings used to compile files. *)
  type t =
    { verbose: int
    (** Verbosity level. *)
    ; loggers: (char * bool) list
    (** Loggers enabled. *)
    ; bflags: bool StrMap.t
    (** Boolean flags. *) }

  (** Stack of saved state for verbosity, loggers and boolean flags. *)
  let saved : t list ref = ref []
  (* NOTE: could be hidden in the signature declaration. *)

  (** [push ()] saves the current state of [verbose], the loggers, and the
      boolean flags, pushing it to the stack. *)
  let push : unit -> unit = fun () ->
    let verbose = !verbose in
    let loggers =
      let fn l = (l.logger_key, !(l.logger_enabled)) in
      List.map fn Stdlib.(!loggers)
    in
    let bflags : bool StrMap.t =
      let fn (_,r) = !r in
      StrMap.map fn Stdlib.(!boolean_flags)
    in
    saved := {verbose; loggers; bflags} :: !saved

  (** [apply st] restores the setting in [st]. *)
  let apply : t -> unit =
    fun {verbose=v; loggers=l; bflags=f} ->
    (* Reset verbosity level. *)
    verbose := v;
    (* Reset debugging flags. *)
    log_enabled := false;
    let reset logger =
      let v = try List.assoc logger.logger_key l with Not_found -> false in
      logger.logger_enabled := v; if v then log_enabled := true;
    in
    List.iter reset Stdlib.(!loggers);
    (* Reset boolean flags. *)
    let reset k (_,r) =
      try r := StrMap.find k f
      with Not_found -> ()
    in
    StrMap.iter reset Stdlib.(!boolean_flags)

  (** [pop ()] restores the settings saved by [push_state], removing it
      from [saved_state]. *)
  let pop : unit -> unit = fun () ->
    let e =
      match !saved with
      | [] -> failwith "[File_management.pop_state] not well-bracketed."
      | e::s -> saved := s; e
    in
    apply e
end
