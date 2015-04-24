Require Import Reals.

Open Scope R.

Inductive Distribution : Set :=
| Bernoulli : { p : R | 0 <= p <= 1 } -> Distribution
| Beta : { α : R | α > 0 } -> { β : R | β > 0 } -> Distribution
| Gaussian : { μ : R | True } -> { σ2 : R | σ2 > 0 } -> Distribution.

Definition support (d : Distribution) : Set :=
  match d with
  | Bernoulli _ => { x : R | x = 0 \/ x = 1 }
  | Beta _ _ => { x : R | 0 < x < 1 }
  | Gaussian _ _ => { x : R | True } (* for symmetry *)
  end.

Definition zer := exist (fun (x : R) => True) 0 I.
Definition one := exist (fun (x : R) => x > 0) 1 Rlt_0_1.
                            
Check (Gaussian zer one).
Eval compute in (support (Gaussian zer one)).

(* if A is a Set, and sig A is some (possibly trivial) refinement where distribution D has support sig A, then x in A can be asserted to be distributed as D and we know that sig A x holds. *)
Definition distributed (x : R) (

