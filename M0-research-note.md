# A sharp finite welfare–incentive frontier with interdependent values

Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

## Mathematical scope

Two agents compete for one object. Agent i observes a pair of binary signals
(s_i,h_i). When i receives the object, its value is a s_i + b h_j, where j
is the other agent; a>0 and b>a are arbitrary real parameters. A nonrecipient
has zero value. The four types of each agent are independent and uniform.
A direct mechanism chooses a lottery at each report profile and real
transfers received by each agent. Utility is quasi-linear. There are no
participation constraints or restrictions on transfer magnitude.

Let ε be a uniform upper bound on the interim utility gain from any
misreport. Let D be ex-ante loss relative to the welfare-maximizing allocation,
with expectation over all sixteen equally likely profiles and the mechanism's
lottery. For every mechanism,

    (b-a) ε + 2a D ≥ a(b-a)/8.

For every θ in [0,1], an ex-post budget-balanced mechanism attains equality,
with ε=a(1-θ)/8 and D=(b-a)θ/16. Consequently, for nonnegative error and
welfare-loss budgets, such a budget-balanced mechanism exists if and only if
the displayed inequality holds. Exact Bayesian incentive compatibility has
minimum expected welfare loss (b-a)/16. Exact efficiency has minimum uniform
incentive error a/8. This is a family with a varying relative externality gap:
changing b/a changes the welfare/error slope, so the result is not simply a
rescaling of the former a=1,b=2 impossibility example.

## Lower bound

Write q(s,o) for agent zero's winning probability at the reported profile.
Consider the two deviations FF→TT and TT→FF for each agent. A type's received
transfer depends on its report and its opponent's report, while the
opponent's distribution is independent of the true type. Thus the transfers
cancel in the sum of the two inequalities for each agent. The combined
value-only cycle sum C is at least −4ε.

Define r(FF)=−a/4, r(TT)=a/4, r(FT)=r(TF)=0. Direct finite-sum algebra gives

    C = Σ_(s,o) (r(s)−r(o)) q(s,o).

For a symmetric efficient rule (splitting ties equally), C=−a/2. At each of
the sixteen profiles, with z in [0,1], the following pointwise inequality
holds, where e is that efficient winning probability, W_k is the welfare
from giving the object to k, and M=max(W_0,W_1):

    (b-a)(r(s)−r(o))z
      ≤ (b-a)(r(s)−r(o))e
        + (a/2)(M−zW_0−(1−z)W_1).

Summing gives (b-a)C≤−a(b-a)/2+8aD. Since b>a, combine this with C≥−4ε
to obtain the theorem. The inequality covers all lotteries, including
inefficient rules and every tie choice. It does not assume budget balance.
The coefficient signs matter: losing welfare at some profiles makes C more
negative, so an absolute coefficient bound would lose the sharp constant.

## Attaining mechanism

Use the symmetric efficient lottery except at the two profiles (FF,TT) and
(TT,FF). Set their agent-zero winning probabilities to 1−θ/2 and θ/2,
respectively. Each crossing profile has welfare gap b−a, giving D=(b-a)θ/16.

Use the same report potential for both agents, in the order FF,FT,TF,TT:

    z = (−b/2+bθ/8, −b/8, −3a/8−b/2, a(1−θ)/8−3b/8).

Agent i receives p_i(t)=z(t_i)−z(t_j). Transfers sum to zero at every report
profile. Each interim transfer is z(own report) minus a report-independent
constant. For either agent, the matrix of ε plus truthful utility minus
misreport utility is

| True type / Report | FF | FT | TF | TT |
|---|---:|---:|---:|---:|
| FF | E | E | F | 0 |
| FT | E | E | F | 0 |
| TF | 0 | F | E | E |
| TT | 0 | F | E | E |

Here E=a(1−θ)/8 and F=a(4−θ)/8. All entries are nonnegative on [0,1], and
some deviations gain exactly E. The asserted incentive error is therefore
the actual maximum, not merely a loose sufficient bound.

## Reusable general theorem

JM.Quantitative treats arbitrary finite own types T, opposing states O, and
outcomes K. It allows arbitrary real payoff and welfare tables, report-indexed
lotteries, and transfers. A balanced nonnegative flow ℓ of deviations cancels
expected transfers. Its coefficient is explicitly computed from payoffs:

    c(r,o,k)=Σ_s [ℓ(r,s)v(r,o,k)−ℓ(s,r)v(s,o,k)].

If α and ν have unit mass, ν is nonnegative, q is a nonnegative normalized
lottery, and the pointwise certificate

    c(r,o,k) ≤ α(r)[β(g(r,o)−W(r,o,k))−A]

holds at every report/state/outcome, then ε-BIC implies

    A ≤ β·welfareLoss + flowMass(ℓ)·ε.

Opponent beliefs ν do not depend on the true own type. The theorem's algebra
does not require α≥0 or β≥0; their probability/loss interpretation requires
those additional semantic conditions. The theorem proves certificate
soundness, not existence or completeness of such certificates. No claim is
made that every finite interdependent-value environment is impossible.

## Relation to sources and novelty limits

Jehiel and Moldovanu, “Efficient Design with Interdependent Valuations,”
Econometrica 69(5), 2001, pp.1237–1259,
https://doi.org/10.1111/1468-0262.00240. The author-hosted February 20, 2000
draft at https://www.econ.uni-bonn.de/micro/en/moldovanu/publications-1/fineff3.pdf
was used to inspect Example 4.2 and Theorem 4.3. This development extends the
finite analogue of Example 4.2 with an exact quantitative characterization.
It does not formalize the continuous generic congruence theorem 4.3,
differentiability, genericity, arbitrary continuous types, nonuniform priors,
or correlated beliefs. Randomization and unrestricted transfers are already
part of the source setting; those features alone are not claimed as novel.

Cyclic-monotonicity necessity and linear certificate/duality arguments are
established mathematics. The authors' earlier Rochet formalization is related
background, not evidence of novelty here. The sharp finite parametric frontier
is derived and checked in this development; no priority, publication novelty,
original-author endorsement, or editorial acceptance is asserted.

## Proof and review status

The library is developed with AI assistance. Separate AI reviewers inspected
the primary source and independently derived rational/symbolic certificates,
including every pointwise inequality and every incentive deviation. Their
reports and reproducible checks accompany the local evidence. This does not
claim independent human review. Lean compilation, selected contract comparison,
axiom audits, external kernel replay, and exact pinned Verso rendering are
recorded separately; none is a hosted Palomar pass or submission authorization.

The former fixed deterministic example remains as a corollary. Its complete
four-type cycle proof remains in the library as a historical independent
certificate; the large unselected helper is not included in Challenge.
