(** High-level compilation functions. *)

open! Lplib

open Timed
open! Scoping
open Scoping.Sign
open! File_management
open File_management.Error
open File_management.Files

open! Core.Debug_console
   
(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [handle_cmd compile ss cmd] adds to the previous [handle_cmd] some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : (Path.t -> Sign.t) -> Sig_state.sig_state -> Parsing.Syntax.p_command ->
  Sig_state.sig_state * Core.Handle.proof_data option * Proof_mode.Queries.result =
 fun compile ss cmd ->
  Rewriting_engine.Print.sig_state := ss;
  try
    let (tm, ss) = Extra.time (Core.Handle.handle_cmd_aux compile ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Extra.Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           ->
      fatal cmd.pos "Uncaught exception [%s]." (Printexc.to_string e)
   
(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Parsing.Syntax.ast = fun fname ->
  match Filename.check_suffix fname src_extension with
  | true  -> Parsing.Parser.parse_file fname
  | false -> Parsing.Parser.Dk.parse_file fname

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
let rec compile : bool -> Path.t -> Sign.t = fun force path ->
  let base = File_management.Files.module_to_file (List.map Parsing.LpLexer.unquote path) in
  let src () =
    (* Searching for source is delayed because we may not need it
       in case of "ghost" signatures (such as for unification rules). *)
    let src = base ^ src_extension in
    let legacy = base ^ legacy_src_extension in
    match (Sys.file_exists src, Sys.file_exists legacy) with
    | (false, false) -> fatal_no_pos "File [%s.{lp|dk}] not found." base
    | (true , true ) -> fatal_no_pos "Both [%s] and [%s] exist." src legacy
    | (true , false) -> src
    | (false, true ) -> legacy
  in
  let obj = base ^ obj_extension in
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" (src ());
      fatal_msg "Dependency stack for module [%a]:\n" Path.pp path;
      List.iter (fatal_msg "  - [%a]\n" Path.pp) !loading;
      fatal_no_pos "Build aborted."
    end;
  if PathMap.mem path !loaded then
    let sign = PathMap.find path !loaded in
    out 2 "Already loaded [%a]\n%!" Path.pp path; sign
  else if force || File_management.Files.more_recent (src ()) obj then
    begin
      let forced = if force then " (forced)" else "" in
      let src = src () in
      out 2 "Loading %s%s ...\n%!" src forced;
      loading := path :: !loading;
      let sign = Scoping.Sig_state.create_sign path in
      let sig_st = Stdlib.ref (Scoping.Sig_state.of_sign sign) in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := PathMap.add path sign !loaded;
      let handle ss c =
        Terms.Meta.reset_key_counter ();
        (* We provide the compilation function to the handle commands, so that
           "require" is able to compile files. *)
        let (ss, p, _) = handle_cmd (compile false) ss c in
        match p with
        | None       -> ss
        | Some(data) ->
            let (st,ts) = (data.pdata_p_state, data.pdata_tactics) in
            let e = data.pdata_expo in
            let st =
              List.fold_left
                (fun st tac -> fst (Proof_mode.Tactics.handle_tactic ss e st tac))
                st ts
            in
            data.pdata_finalize ss st
      in
      let consume cmd = Stdlib.(sig_st := handle !sig_st cmd) in
      Stream.iter consume (parse_file src);
      Sign.strip_private sign;
      if Stdlib.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked %s\n%!" src; sign
    end
  else
    begin
      out 2 "Loading %s ...\n%!" (src ());
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> ignore (compile false mp)) !(sign.sign_deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded %s\n%!" obj; sign
    end

(** [recompile] indicates whether we should recompile files who have an object
    file that is already up to date. Note that this flag only applies to files
    that are given on the command line explicitly, not their dependencies. *)
let recompile = Stdlib.ref false

(** [compile_file fname] is the main compiling function. It is called from the
    main program exclusively. *)
let compile_file : file_path -> Sign.t = fun fname ->
  Package.apply_config fname;
  (* Compute the module path (checking the extension). *)
  let mp = File_management.Files.file_to_module fname in
  (* Run compilation. *)
  compile Stdlib.(!recompile) mp

(** Pure wrappers around compilation functions. Functions provided perform the
    same computations as the ones defined earlier, but restores the state when
    they have finished. An optional library mapping or state can be passed as
    argument to change the settings. *)
module Pure : sig
  val compile : ?lm:string -> ?st:State.t -> bool -> Path.t -> Sign.t
  val compile_file : ?lm:string -> ?st:State.t -> file_path -> Sign.t
end = struct

  (* [pure_apply_cfg ?lm ?st f] is function [f] but pure (without side
     effects).  The side effects taken into account occur in
     {!val:File_management.State.t}, {!val:File_management.File_management.Files.lib_mappings} and in the meta
     variable counter {!module:Terms.Meta}. Arguments [?lm] allows to set the
     library mappings and [?st] sets the state. *)
  let pure_apply_cfg : ?lm:string -> ?st:State.t -> ('a -> 'b) -> 'a -> 'b =
    fun ?lm ?st f x ->
    let libmap = !lib_mappings in
    State.push ();
    Option.iter new_lib_mapping lm;
    Option.iter State.apply st;
    let restore () =
      State.pop ();
      lib_mappings := libmap
    in
    try
      let res = f x in
      restore (); res
    with e -> restore (); raise e

  let compile ?lm ?st force path =
    let f (force, path) = compile force path in
    pure_apply_cfg ?lm ?st f (force, path)

  let compile_file ?lm ?st = pure_apply_cfg ?lm ?st compile_file
end

(** [reset_default ()] resets the verbosity level and the state of the loggers
    to their default value (configurable by the user with command line flags).
    The boolean flags are also reset to their default values. *)
let reset_default : unit -> unit = fun () ->
  (* Reset verbosity level. *)
  verbose := Stdlib.(!default_verbose);
  (* Reset debugging flags. *)
  log_enabled := false;
  let reset l =
    let v = String.contains Stdlib.(!default_loggers) l.logger_key in
    l.logger_enabled := v; if v then log_enabled := true;
  in
  List.iter reset Stdlib.(!loggers);
  (* Reset flags to their default values. *)
  let reset _ (default, r) = r := default in
  Extra.StrMap.iter reset Stdlib.(!boolean_flags)
