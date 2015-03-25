(* The notion of a closed term would be good. A program is a term closed by the empty environment and every reduction should maintain the invariant that the term is closed by its environment. Closures would carry this proof with them. *)

Parameter var : Set.

Axiom var_eq_dec : forall (x y : var), { x = y } + { ~ x = y }.

Inductive term : Set :=
| Ref : var -> term
| Abs : var -> term -> term
| App : term -> term -> term
with value : Set :=
| Closure : term -> env -> value
with env : Set :=
| NullEnv : env
| ConsEnv : var -> value -> env -> env.

Inductive closes : env -> term -> Prop :=
  FreeVar : forall (x : var) (v : value), 

