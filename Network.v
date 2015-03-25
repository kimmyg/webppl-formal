Require Import List.

Parameter Value : Set.

Inductive Node : Set :=
| Degenerate : Value -> Node
| Random : list Node -> Node
| Multiplexer : Node -> Node -> Node -> Node.

(* 

Every function body expresses the flow of values from sources---parameters and inner function calls---to sinks--arguments and results. A static analysis like CFA2 can not only link up these flows but also can identify values within the program that follow a stack discipline and handle them exactly. Using this information to resolve the inter-functional flow allows the creation of an abstract network.

I'll try to illustrate with an example. The program

(sample bernoulliERP 1/2)^ℓ0

consists solely of a sample statement. The first argument, bernoulliERP, indicates that this sample will be drawn from a distribution in the bernoulli family, and that distribution is identified by the second argument, 1/2. This sample statement, like each callsite, is labelled. A combination of these labels uniquely identifies each sample operation during evaluation of the program (even if the same sample site is revisited).

The distribution denoted by this program is simply Bernoulli(1/2), and the Markov network corresponding to this distribution is simply a single node.

Now consider the program

(sample bernoulliERP (sample betaERP 1 1)^ℓ0)^ℓ1

This program samples from a beta distribution and uses the result to parameterize a sample from a bernoulli distribution. If the beta distribution is represented by node A, and the bernoulli by node B, the Markov network corresponding to this program is A -> B; this network is precise.

Not every probabilistic program corresponds to a concrete Markov network. For instance, we can express a geometric distribution as a process built on the simpler bernoulli distribution:

(fix geom (λ (p) (if0 (sample bernoulliERP p)^ℓ0 (+ 1 (geom p)^ℓ1)^ℓ2 0)))
(geom 1/2)^ℓ3

The occurrence of if0 in this program serves to condition (in the probabilistic sense) the distribution of the condition (in the syntactic sense) and is represented in the Markov network by a multiplexer node, a node which selects from two distributions based on the value of this condition.

The number of times this process recurs is unbounded (though every performance converges almost surely), so the network induced by this program is infinite.

Here's an ascii art representation.

+-+  +-+  +-+  +-+
| |->| |->| |->| |-> ...
+-+  +-+  +-+  +-+
 |    |    |    |
 v    v    v    v
 0    1    2    3

While the representation is infinite, the description of the representation isn't; there is a lot of structure to exploit. This leads to the "abstract" network representation

    +------+
    |      |
+-+ |  +-+ |
| |-+->| |-+
+-+    +-+  
 |      |   
 v      v   
 0     num

The edges can be annotated with the change in structure that occurs as each is traversed.

 *)
