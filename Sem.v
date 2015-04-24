(* WebPPL Semantics

WebPPL allows the expression of generative models: a finite evaluation of a WebPPL program results in a sample from the distribution defined by the program.

- a constant evaluates to a degenerate distribution
- a function call evaluates to the distribution of its result
- a conditional expression evaluates to a multiplexer distribution
- an environment stores distributions

CPS, like the monad, lifts the randomness out of the value and applies it the continuation, kind of.

E[((if (flip 1/2) (λ (x) #t) flip) (beta 1 1))]
λk. flip 1/2 λ.f beta 1 1 λb. if f then λx k.(k 1) b k else flip b k

define f() if0 flip(1/2)ᴬ then λx.0 else flip
f()ᴮ(beta(1,1)^C)ᴰ

Higher-orderness

λk.f(λg.beta(1,1,λb.g(b)ᴰ)^C)ᴮ
from the point of the call, we analyze the called body and get a result λx.0 with fragment true(result(A),const(λx.0)).

how do we lift a distribution over operators to a distribution over results?

((if C λ0 λ1) X) -> if C (λ0 X) (λ1 X)
But this isn't a syntactic or static property.

when we get to a function call, we have distributions over the operator and operands.
we want to lift the distribution of the operator over the distribution of results.

 E[(flip (if (flip 1/2) (beta 1 1) (beta 2 2)))]


The soundness theorem for dependence?

Create a semantics that tracks dependence /or/ create a correspondence between some semantic rules and induced dependence
Show that the dependence extracted from the control flow graph respects the semantic abstraction, that every dependence in the actual program is captured by the abstract semantic dependencies.

We need a judgement: value v₀ depends stochastically on value v₁
and an corresponding abstract judgement: abstract value v₀ depends stochastically on abstract value v₁ meaning that (some or all) values abstracted by v₀ are dependent on some or all values abstracted by v₁.

Let's start with the obvious case, a sample operation.
The result of such an operation depends stochastically on its arguments.
If any of the arguments is stochastic, then the result depends on that stochastic component which is manifest according to its formation.
Suppose we have a joint distribution on our environment.
Suppose that we have P(X) and we would like to know the distribution of Z=sample(flip,X).
P(X,Z)=P(Z|X)P(X)
If X is actually

(flip A (beta B 1 1))
(λ (k) (beta B 1 1 (λ (r0) (flip A r0 k))))
P()
P(r0)
P(

if (flip A 1/2) then (flip B 1/3) else (flip C 1/5)
