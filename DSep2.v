Parameter R : Set.

(* Node Types

Nodes capture the generation or combination of values within a program.
Edges, which represent stochastic dependence, are induced by value flow during evaluation.
For instance, each "evaluation" of a constant in the program is represented by a constant node.
Constant nodes behave like degenerate random variables: they take on a single value with certainty (i.e., probability 1).
A sampling operation is a random variable and is represented by such a node.
A deterministic function is represented by a distinct type of node depending on the properties of the function.
For instance, the constant function is deterministic but its node is functionally equivalent to a constant node and should be so treated.
Injective functions, on the other hand, are essentially transparent in the determination of D-connectedness and are treated specially in this regard.
Finally, conditional expressions, as expressions, have a "result" with a distribution and so can be represented a node: multiplexer nodes select an output distribution on a condition distribution.
Multiplexer nodes evoke dependent types: just as the type of a dependently-typed function depends on the value of its input, the family of the output distribution of a multiplexer node depends on the value of the selector distribution.
