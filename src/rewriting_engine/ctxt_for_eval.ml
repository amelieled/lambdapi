
open Scoping.Terms
open Scoping.Env
   
(** [of_prod c n t] returns a tuple [(env,b)] where [b] is constructed
   from the term [t] by unbinding [n] dependent products. The free variables
   created by this process are given (with their types) in the environment
   [env] (in reverse order). For instance, if [t] is of the form [Πx1:a1, ⋯,
   Πxn:an, b] then the function returns [b] and the environment [(xn,an);
   ⋯;(x1,a1)]. [n] must be non-negative.
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod : ctxt -> int -> term -> env * term = fun c n t ->
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf c t with
    | Prod(a,b) ->
        let (x, b) = Bindlib.unbind b in
        build_env (i+1) (add x (lift (Eval.simplify [] a)) None env) b
    | _         -> invalid_arg __LOC__
  in
  build_env 0 [] t

(** [of_prod_using c xs t] is similar to [of_prod c n t] where [n =
   Array.length xs] except that it does not return the final codomain [b] and
   replaces unbound variables by those of [xs].
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod_using : ctxt -> tvar array -> term -> env = fun c xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env else
    match Eval.whnf c t with
    | Prod(a,b) -> let env = add xs.(i) (lift a) None env in
                   build_env (i+1) env (Bindlib.subst b (Vari(xs.(i))))
    | _         -> invalid_arg __LOC__
  in
  build_env 0 [] t
