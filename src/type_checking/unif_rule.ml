(** Symbols and signature for unification rules. *)

open Data_structure.Terms
open Data_structure.Sign
open! Data_structure
   
(** Symbol representing an atomic unification problem. The term [equiv t
    u] represents [t ≡ u]. The left-hand side of a unification rule is
    made of only one unification. *)
let equiv : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = ("≡", Pratter.Neither, 1.1, File_management.Pos.none (path, "#equiv")) in
  let sym =
    Sign.add_symbol ghost_sign Public Defin Eager (File_management.Pos.none "#equiv") Kind []
  in
  Sign.add_binop ghost_sign sym bo;
  sym

(** Cons-like symbol for equivalences. The right-hand side of a unification
    rule is made of a list of the form
    [cons (equiv t u) (cons (equiv v w) ...)] pretty-printed
    [t ≡ u; v ≡ w; ...]. *)
let cons : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = (";", Pratter.Right, 1.0, File_management.Pos.none (path, "#cons")) in
  let sym =
    Sign.add_symbol ghost_sign Public Defin Eager (File_management.Pos.none "#cons") Kind []
  in
  Sign.add_binop ghost_sign sym bo;
  sym

(** [unpack eqs] transforms a term of the form
    [cons (equiv t u) (cons (equiv v w) ...)]
    into a list [[(t,u); (v,w); ...]]. *)
let rec unpack : term -> (term * term) list = fun eqs ->
  match Basics.get_args eqs with
  | (Symb(s), [v; w]) ->
      if s == cons then
        match Basics.get_args v with
        | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
        | _          (* Ill-formed term. *) -> assert false
      else if s == equiv then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                 -> assert false (* Ill-formed term. *)

(** [is_ghost s] is true iff [s] is a symbol of the ghost signature. *)
let is_ghost : sym -> bool = fun s -> s == equiv || s == cons
