Parameter Node : Set.

Parameter direct : Node -> Node -> Prop.

Definition indirect (A B : Node) : Prop := (direct A B) \/ (direct B A).

Definition collider (C A B : Node) : Prop := (direct A C) /\ (direct B C).

Parameter conditioned : Node -> Prop.

Inductive connected (A B : Node) : Prop :=
| CImmediate : indirect A B -> connected A B
| CDistant : (exists (C : Node), indirect A C /\ connected C B) -> connected A B.

Inductive descendant (A B : Node) : Prop :=
| DImmediate : direct B A -> descendant A B
| DDistant : (exists (C : Node), direct B C /\ descendant A C) -> descendant A B.

Inductive connector (A : Node) : Prop :=
| ConnNonCollider : 

Inductive dconnected (A B : Node) : Prop :=
| DCImmediate : indirect A B -> ~ conditioned A -> ~ conditioned B -> dconnected A B
|                                                                                  
| DCDistant : (exists (C : Node), dconnected A C                                                                                 


