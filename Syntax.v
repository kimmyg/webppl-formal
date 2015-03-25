Inductive Identifier : Set := id : nat -> Identifier.

Inductive BinaryOperator : Set := .
Inductive LogicalOperator : Set := .
Inductive UnaryOperator : Set := .

Inductive Expression : Set :=
| FunctionExpression : option Identifier -> list Identifier -> Expression
| CallExpression : Expression -> list Expression -> Expression
| ConditionalExpression : Expression -> Expression -> Expression -> Expression
| ArrayExpression : list Expression -> Expression
| MemberExpression : Expression -> Identifier -> Expression
| BinaryExpression : BinaryOperator -> Expression -> Expression -> Expression
| LogicalExpression : LogicalOperator -> Expression -> Expression -> Expression
| UnaryExpression : UnaryOperator -> Expression -> Expression
| ObjectExpression : list ObjectProperty -> Expression
| ReferenceExpression : Identifier -> Expression
| SampleExpression : Expression -> list Expression -> Expression                                        
with Statement : Set :=
| EmptyStatement : Statement
| BlockStatement : list Statement -> Statement
| ExpressionStatement : Expression -> Statement
| IfStatement : Expression -> Statement -> option Statement -> Statement
| ReturnStatement : option Expression -> Statement
with ObjectProperty : Set := objectProperty : Identifier -> Expression -> ObjectProperty.

Parameter R : Set.

Inductive value : Set :=
| Number : R -> value
| Boolean : bool -> value.

Definition nat_eq_dec : forall (x y : nat), {x = y} + {~ x = y}.
Proof.
intros x.
induction x.
intros y.
destruct y.
left. reflexivity.
right.
intros contra.
inversion contra.
intros y.
destruct y.
right. intros contra. inversion contra.
destruct IHx with (y := y).
left. rewrite -> e. reflexivity.
right. intros Heq. inversion Heq.
apply n. apply H0.
Defined.

Definition Identifier_eq_dec : forall (x y : Identifier), {x = y} + {~ x = y}.
Proof.
  intros x.
induction x.
intros y.
induction y.
admit.
Defined.

Definition env := Identifier -> option value.
Definition empty_env : env := fun x => None.
Definition env_extend (e : env) (y : Identifier) (v : value) : env :=
  fun (x : Identifier) => if Identifier_eq_dec x y then Some v else (e x).
