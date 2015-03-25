Require Import List.

Parameter Value : Set.

Inductive Node : Set :=
| Degenerate : Value -> Node
| Random : list Node -> Node
| Multiplexer : Node -> Node -> Node -> Node.

