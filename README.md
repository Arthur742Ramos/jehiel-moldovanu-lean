# Continuous binary implementation and a sharp finite frontier


The main continuous-domain result characterizes efficient Bayesian
implementation with two alternatives. On an own-type domain containing an
open ball, a nonzero social coefficient and one active welfare cut force
private coefficients to be a nonnegative multiple of social coefficients.
The theorem covers arbitrary independent opponent probability laws,
including atoms, and unrestricted integrable received transfers. Explicit
transfers establish the converse with truthful opponents held fixed.

The concrete continuous auction uses actual independent uniform-square
signals and winning value a*own_first_signal+b*other_second_signal.
Efficiency is impossible even with only agent 0 incentive compatibility
for every a,b>0. See [the continuous note](M1-continuous-note.md) for exact
measurability, integrability, domain, tie and prior assumptions.

A separate finite theorem retains binary types, a>0,b>a and independent
uniform priors.
Every ε-BIC mechanism with expected welfare loss D satisfies

    (b-a) ε + 2a D ≥ a(b-a)/8.

Budget-balanced mechanisms attain every frontier point. For nonnegative
error and loss budgets the inequality exactly characterizes feasibility.
Exact BIC has minimum welfare loss (b-a)/16. The original a=1,b=2,
deterministic impossibility theorem is retained as a corollary.

The continuous theorem is a binary congruence subtheorem of the
Jehiel–Moldovanu program. It does not prove the arbitrary-alternative
Theorem 4.3 or genericity. The finite frontier is a separate quantitative
extension of the analogue of Example 4.2. No mathematical novelty or editorial acceptance is claimed.
See [the research note](M0-research-note.md) for definitions, derivation,
attaining transfers, source relation, and scope limits.

- `JM/Defs.lean`: the original model and full four-type certificate.
- `JM/Quantitative.lean`: reusable balanced-flow certificate soundness.
- `JM/Sharp.lean`: parametric sharp bound and budget-balanced witnesses.
- `JM/Frontier.lean`: complete feasibility and exact-BIC welfare cost.
- `JM/Corollaries.lean`: original deterministic contract as a corollary.
- `JM/Binary.lean`: continuous-domain necessity and explicit-transfer equivalence.
- `JM/ContinuousAuction.lean`: genuine uniform-square law, value/welfare bridges and impossibility.
- `Challenge.lean`: standalone definitions and selected statement holes.
- `Solution.lean`: imports the admission-free reusable library.

Build with the pinned toolchain and Mathlib version:

    LEAN_NUM_THREADS=1 lake build JM Challenge Solution

The scripts and evidence distinguish local functional verification from
exact-SHA hosted gates. The dispatch-only proof and rendering workflows use
the pinned official pipeline. Publication and merge have been authorized;
Palomar intake and registration require separate authorization. Hosted results
must be checked against their exact commit and authoritative artifacts.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
