# Sharp finite welfare–incentive frontier

Lean proofs for a two-agent interdependent-value model with binary
multidimensional types, arbitrary own gap a>0 and external gap b>a,
independent uniform priors, and randomized allocations.

Every ε-BIC mechanism with expected welfare loss D satisfies

    (b-a) ε + 2a D ≥ a(b-a)/8.

Budget-balanced mechanisms attain every frontier point. For nonnegative
error and loss budgets the inequality exactly characterizes feasibility.
Exact BIC has minimum welfare loss (b-a)/16. The original a=1,b=2,
deterministic impossibility theorem is retained as a corollary.

The result is a finite quantitative extension of the analogue of
Jehiel–Moldovanu Example 4.2, not their continuous generic impossibility
theorem. No mathematical novelty or editorial acceptance is claimed.
See [the research note](M0-research-note.md) for definitions, derivation,
attaining transfers, source relation, and scope limits.

- `JM/Defs.lean`: the original model and full four-type certificate.
- `JM/Quantitative.lean`: reusable balanced-flow certificate soundness.
- `JM/Sharp.lean`: parametric sharp bound and budget-balanced witnesses.
- `JM/Frontier.lean`: complete feasibility and exact-BIC welfare cost.
- `JM/Corollaries.lean`: original deterministic contract as a corollary.
- `Challenge.lean`: standalone definitions and selected statement holes.
- `Solution.lean`: imports the admission-free reusable library.

Build with the pinned toolchain and Mathlib version:

    LEAN_NUM_THREADS=1 lake build JM Challenge Solution

The scripts and evidence distinguish local functional verification from the
later required exact-SHA hosted gates. The workflow is prepared locally only;
no push, dispatch, registry submission, or external change is authorized.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
