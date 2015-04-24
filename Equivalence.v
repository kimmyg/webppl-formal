Require Import Rbase.

Inductive var := Var : nat -> var.

Inductive term : Set :=
| Ref : var -> term
| Abs : var -> term -> term
| App : term -> term -> term
| If0 : term -> term -> term
| Num : R -> term.

Fixpoint cps (e : term) (κ : kont) :=
  match e with
  | Ref n => KApp κ (CPSRef n)
  | Abs x e => KApp κ (CPSAbs x κRef (cps e κRef))
                    | App f e => cps f (κAbs y (cps e (κAbs z (UApp

Inductive cpsterm : Set :=
| CPSRef : var -> cpsterm
| CPSAbs : var -> var -> cpsterm -> cpsterm
                                      | 