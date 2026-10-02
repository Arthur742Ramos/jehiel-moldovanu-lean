# Jehiel–Moldovanu Impossibility in Lean 4

Lean 4 / Mathlib formalization of a **finite instance** of the Jehiel–Moldovanu
impossibility theorem (Jehiel & Moldovanu, *Econometrica* 69(5), 1237–1259, 2001;
DOI `10.1111/1468-0262.00240`): with multidimensional types and interdependent
valuations, ex post efficiency, Bayesian incentive compatibility, and budget
balance are jointly unattainable. This is the impossibility flip side of the
AGV possibility result.

## The instance

- Two agents (`Agent := Fin 2`), each with a two-dimensional binary type
  (`T i := Bool × Bool`).
- One object; the winner is in `X := Fin 2`.
- Agent `i`'s winning value is `valA` of its own first signal (`0` or `1`) plus
  `valB` of the other agent's second signal (`0` or `2`), scaled by `c = 1`;
  the nonwinner's value is zero. Values are interdependent.
- Priors are independent and uniform (`uniformPrior`).

## Main theorem

```lean
theorem JM.jehiel_moldovanu_impossibility :
  ∀ (x : JM.Allocation) (p : JM.Transfers),
    JM.IsEfficient x → JM.IsBIC JM.uniformPrior x p → JM.IsBudgetBalanced p → False
```

- `IsEfficient` is pointwise: the allocation maximizes utilitarian welfare at
  every profile.
- `IsBIC` is interim: truthful reporting maximizes each agent's interim
  expected utility at every own type, under the fixed prior `uniformPrior`.
- `IsBudgetBalanced` is pointwise: transfers sum to zero at every report
  profile.
- The statement takes no prior argument; the prior is fixed to `uniformPrior`.

## Proof idea

A four-type cycle congruence argument over the cycle
`(false,false) → (false,true) → (true,true) → (true,false) → (false,false)`:

1. Transfer terms telescope around each agent's closed four-type cycle, so
   each agent's cycle sum with arbitrary transfers equals the zero-transfer
   `cycleSum`.
2. BIC forces each agent's cycle sum to be nonnegative.
3. For every efficient rule, the two agents' value-only cycle sums total
   `-1/2`: twelve profiles have forced winners, and the four diagonal
   profiles are efficiency ties, handled by a sixteen-way case split
   (`scripts/verify_cycle.py` independently enumerates all sixteen
   tie-breaking choices and checks the sum).
4. The two facts contradict each other (`linarith`).

Budget balance is a hypothesis of the statement but is not needed for the
contradiction, since the telescoping is per-agent. This is a finite instance,
not the continuous generic impossibility theorem of the original paper.

## Status

Builds green with `lake build` (Lean v4.35.0-rc2); zero `sorry` in the library;
the theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Prior art: a Palomar registry search on 2026-10-02 for "jehiel", "moldovanu",
"interdependent valuations", and "multidimensional" returned zero results.

Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. License: BSD-3-Clause.
