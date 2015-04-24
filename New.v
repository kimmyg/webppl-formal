Require Import Reals.

Inductive X : Set := Var : nat -> X.
Inductive ℓ : Set := Lab : nat -> ℓ.

Inductive erp : Set :=
| beta : erp
| flip : erp
| gaussian : erp.

Inductive prim : Set :=
| Plus : prim
| Minus : prim
| Times : prim.
            
Inductive C : Set :=
| Num : R -> C
| ERP : erp -> C
| Prim : prim -> C
| Ref : X -> C
| Lam : list X -> C -> C
| App : C -> list C -> ℓ -> C
| Let : X -> C -> C -> C
| Fix : C -> C.

Inductive V : Set :=
| NumV : R -> V
| Clos : C -> E -> V
                          
with E : Set :=
| EnvEmp : E
| EnvExt : X -> V -> E -> E.

Inductive K : Set :=
| Halt : K
| LetK : X -> E -> C -> list ℓ -> K -> K
| RatK : E -> list C -> ℓ -> list ℓ -> K -> K
| RanK : V -> list V -> E -> list C -> ℓ -> list ℓ -> K -> K.

Inductive CEIK : Set :=
| CEIKEval : C -> E -> list ℓ -> K -> CEIK
| CEIKAppl : K -> V -> CEIK.

Inductive reduces : CEIK -> CEIK -> Prop :=
| ENum : forall (r : R) (ρ : E) (ι : list ℓ) (κ : K), reduces (CEIKEval (Num r) ρ ι κ) (CEIKAppl κ (NumV r))
                                                              | ERef : forall 
                                                     
                                                     
                          

                              

(*

Xiables
