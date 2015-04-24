(*

The "result" of a probabilistic program is a sample from its distribution.
If we consider random choices as random black boxes, each run of the program realizes a particular path in the reduction relation.
We can make the reduction relation deterministic by factoring out the stochastic behavior and parameterizing it by what was factored out.
This is the sense in which a control-flow analysis can help us reason about programs: the soundness of such an analysis guarantees that all possible paths are explored and accounted for.
Thus, when extracting dependence that could occur on all possible paths, the realized dependence must lie within the extracted.
We can conjecture that a probabilistic program corresponds to an infinite Bayesian network---infinite in both height and width---and that any converging evaluation corresponds to a path through this network.
We don't need to show the program-network correspondence; merely showing that we account for all possible dependencies is sufficient.

 *)

(*

(sample e es ...)
if E[[e]] => d and E[[es]] ... => vs ..., and if sample(d,vs,...)=v then vs ... are connected to v toward v
(if e0 e1 e2)
if E[[e0]] => v0 =/= #f and E[[e1]] => v1, then v1, as the result of the entire expression, is connected to v0
if E[[e0]] => v0 = #f and E[[e2]] => v2, then v2, as the result of the entire expression, is connected to v0
x
E[[x,\rho]] -> \rho(x)

(let ([x e0]) e1)

