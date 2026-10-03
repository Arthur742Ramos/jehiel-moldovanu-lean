# Binary implementation with continuous multidimensional signals

Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

This development formalizes a continuous-domain private/social coefficient
congruence theorem for two alternatives, with a matching explicit-transfer
construction. It accompanies the independently proved sharp finite
welfare/incentive frontier in `M0-research-note.md`. The two results have
different domains; neither is presented as a logical corollary of the other.

The economic background is Jehiel and Moldovanu,
[Efficient Design with Interdependent Valuations](https://doi.org/10.1111/1468-0262.00240),
Econometrica 69(5), 1237–1259 (2001). The primary text actually inspected is
the [author-hosted February 20, 2000 draft](https://www.econ.uni-bonn.de/micro/en/moldovanu/publications-1/fineff3.pdf),
Section 2, Theorem 4.3 and its appendix. This is a binary subtheorem of the
congruence program, proved through two incentive inequalities rather than
moving-boundary differentiation. It does not formalize the arbitrary-number-
of-alternatives result, a genericity/measure-zero result, or a published-paper
correction. No mathematical novelty or original-author endorsement is claimed.

## Primitive model and theorem

One distinguished agent has a true signal and report in a set U of a real
normed vector space E. U contains a ball of positive radius around t₀.
The theorem quantifies every admissible true type and every report; it does
not assume an own-type prior or replace this binder with an almost-everywhere
incentive condition. Finite-dimensional Euclidean spaces are special cases.
For another agent's information, or a joint state of any number of opponents,
Ω is an arbitrary measurable space with a probability measure μ. That same
measure appears at every true type: opposing beliefs are independent of the
agent's own information.

There are exactly two alternatives, labeled 0 and 1. Alternative-0 private
value is g(t,o). The private value difference is c(t)+d(o), where c is a real
linear functional. Social welfare difference is A(t)+H(o), where A is another
linear functional with A≠0. General statements take these affine differences
as the model's primitives; the auction corollary derives them from actual
agent valuations and their summed welfare. The own linear functionals need
not be continuous: only directional perturbations are used.

A report-profile lottery q(r,o) is a probability in [0,1], measurable in o
at every report r. Received transfers p(r,o) are integrable at every report.
The functions g(t,·) and d are integrable, so every expected utility

\[
 U(t,r)=\int [g(t,o)+q(r,o)(c(t)+d(o))+p(r,o)]\,d\mu(o)
\]

is integrable. `utility_integrable` proves this property before any incentive
argument uses the integral. Thus none of the results exploit Bochner
integral totalization on undefined expectations. The social shock H is measurable, making the active bands measurable
events. For constructive existence, H is also integrable. Lottery measurability is per report;
no joint report/state measurability or allocation continuity is claimed.

Efficiency means q=1 when A(r)+H(o)>0, q=0 when it is negative, and any
probability in [0,1] at equality. This condition is pointwise in every opposing
state of the model. BIC means U(t,r)≤U(t,t) for all t,r∈U.
Budget balance, participation, transfer bounds and individual rationality are
absent. Transfers have no differentiability restriction.

The explicit active-threshold condition is

\[
 \forall\eta>0,\quad
 \mu\{o:|A(t_0)+H(o)|<\eta\}>0.
\]

It allows a positive-probability atom at the cut, continuous densities,
nonuniform laws and singular laws. No atomlessness, density, CDF
differentiability, convexity of the entire type domain, or global positive
interim winning probability is required.

Under these assumptions, efficient BIC implementation is possible exactly
when

\[
 c=\lambda A\quad\text{for some }\lambda\ge0.
\]

`congruence` proves necessity for every regular mechanism.
`implementation_iff` characterizes integrable transfers for every specified
measurable efficient lottery. `efficient_bic_exists_iff` also supplies an
actual efficient measurable allocation witness, the social threshold rule;
its existence statement is therefore not vacuous. Zero private coefficient
c is included with λ=0. A=0 is excluded. Removing the active-cut or open-ball
condition can permit a constant efficient allocation with misaligned
coefficients, so those hypotheses are substantive.

## Necessity and construction

Integral linearity gives

\[
 U(t,r)=B(t)+c(t)Q(r)+R(r),\qquad Q(r)=\int q(r,o)\,d\mu(o),
\]

with a report-only R. Adding BIC for t against s and s against t cancels R:

\[
 [c(t)-c(s)][Q(t)-Q(s)]\ge0.
\]

For any direction h with A(h)>0, choose δ>0 so t₀±δh belong to the ball.
Efficiency makes q(t₀+δh,o)≥q(t₀−δh,o) everywhere. On the positive-mass
event |A(t₀)+H(o)|<δA(h), the first probability is 1 and the second 0.
Thus Q strictly increases, independently of how endpoint ties are resolved.
The incentive inequality gives c(h)≥0. Reversing h establishes
c(h)A(h)≥0 for every h.

Normalize one vector w so A(w)=1. If A(v)=0 but c(v)≠0, then
w−[(c(w)+1)/c(v)]v has social projection 1 and private projection −1,
a contradiction. Hence ker A⊆ker c, and decomposing an arbitrary vector
along w yields c=c(w)A with c(w)≥0. This argument needs no envelope or
Hessian theorem.

Conversely, if c=λA with λ≥0, define received transfers

\[
 p(r,o)=[\lambda H(o)-d(o)]q(r,o).
\]

True utility becomes g(t,o)+λq(r,o)[A(t)+H(o)]. The truthful efficient
allocation maximizes it pointwise. The transfers are proved integrable using
the bounded lottery and integrable d,H. This is ex-post IC with opponents
held at their actual types, and therefore BIC. It is not dominant-strategy
truthfulness under arbitrary false opponent reports in an interdependent-
value game. Arbitrary efficient tie lotteries are covered.

## Continuous auction consequence

The concrete corollary has two agents whose independent types (sᵢ,hᵢ)
are genuinely uniform on (0,1)². The prior is natural subtype Lebesgue volume;
its mass is proved to be one. Winner i receives a sᵢ+b hⱼ and the loser
receives zero. Welfare is the sum of the two agents' actual values.
The impossibility applies for every a>0,b>0, with unrestricted integrable
received transfers and lotteries. Only agent 0's BIC inequalities are needed;
therefore any mechanism satisfying both agents' BIC conditions is also ruled
out. No a<b restriction is needed on this continuous domain.

For agent 0, taking alternative 1 to give the object to agent 0 yields
c=(a,0), A=(a,−b), d(o)=b h₁ and H(o)=b h₁−a s₁. The midpoint is interior.
For every η>0 a sufficiently small opponent box around (1/2,1/2) has strictly
positive measured area and lies inside |A(t₀)+H|<η. This verifies active
support against the actual uniform-square law. Alignment is impossible:
its first coordinate would give λ=1 and its second λ=0.

This changes the own-type domain from the old four points to an open square.
It does not remove a<b from the existing finite theorem or imply the finite
sharp welfare/error bounds. The finite frontier and its budget-balanced
attaining mechanisms remain separate, preserved results.

## Verification boundary

The library and Solution must be admission-free with only standard axioms.
Challenge repeats genuine definitions and selected contracts without importing
local implementation modules. Independent mathematical, exact-source and
prose-to-binder reviews and local Comparator, three-kernel and pinned renderer
results belong to the accompanying evidence bundle. Passing those gates is
not a hosted exact-SHA pass, editorial acceptance, registration, publication
readiness, or an independent human referee report. Publication and merge
checks are recorded separately against exact immutable commits; Palomar
intake and registration are outside that authorization.
