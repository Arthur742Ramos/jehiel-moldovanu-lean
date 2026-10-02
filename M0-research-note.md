# M0 Research Note: Jehiel–Moldovanu Impossibility (2026-10-02)

## Paper

Philippe Jehiel & Benny Moldovanu (2001), "Efficient Design with Interdependent
Valuations," *Econometrica* 69(5), 1237–1259. DOI: 10.1111/1468-0262.00240.

## Main result (continuous version)

In a social choice setting with interdependent valuations (informational and
allocative externalities), efficient Bayes–Nash incentive compatible mechanisms
exist only if a "congruence condition" relating private and social rates of
information substitution holds. With multidimensional signals, this is an
integrability constraint that generically fails (holds only if values are
private or under symmetry). With one-dimensional signals it reduces to
monotonicity and can generically hold.

## Finite formalization plan

This is the impossibility flip side of the AGV arc: AGV showed efficiency + BIC
+ budget balance ARE jointly possible with independent one-dimensional types;
Jehiel–Moldovanu shows they become impossible with multidimensional types.

### Setting (finite)

- 2 agents (Fin 2), 1 indivisible object, X = Fin 2 (who gets it).
- Each agent i has a TWO-DIMENSIONAL binary type: t_i = (a_i, b_i) ∈ {L,H}².
- INTERDEPENDENT values:
  - v_1(t) = A(a_1) + c * B(b_2)  [own a-signal + other's b-signal]
  - v_2(t) = A(a_2) + c * B(b_1)
  with A(H) > A(L) ≥ 0, B(H) > B(L) ≥ 0, c > 0.
- Independent priors: uniform on {L,H}² for each agent.

The b_i signal is the multidimensionality: it is payoff-irrelevant to agent i
(does not enter v_i) but payoff-relevant to the other agent (enters v_j).
This is the finite analog of the paper's multidimensional-signal setting.

### Theorem (finite JM impossibility)

For suitable explicit (A, B, c) — to be determined, with A(H)-A(L),
B(H)-B(L), c chosen so the cycle below bites — there is NO mechanism (x, p)
that is simultaneously:
1. Ex post efficient: x(t) ∈ argmax_{k ∈ Fin 2} v_k(t) for all t.
2. Bayesian incentive compatible (interim, with truthful others).
3. Ex post budget balanced: p_1(t) + p_2(t) = 0 for all t.

### Proof skeleton (discrete congruence / cycle condition)

The paper's integrability (congruence) condition becomes a CYCLE inequality in
the finite setting — directly analogous to Rochet's cyclic monotonicity:

1. Efficiency pins down x = xmax (welfare-maximizing rule). This is forced.
2. BIC for agent 1: for true type s and report r,
   U_1(r|s) ≤ U_1(s|s), where U is interim expected utility.
3. Consider the 4-cycle in agent 1's type space:
   (L,L) → (H,L) → (H,H) → (L,H) → (L,L).
   Summing the four BIC inequalities around this cycle, the transfer terms
   telescope (each p_1 term appears once positively, once negatively).
4. What remains is a pure efficiency condition: a sum of value-difference
   terms that must be ≥ 0 for BIC but is < 0 given the interdependent values
   and the efficient allocation rule. Contradiction.
5. Budget balance is not even needed for the core contradiction (it
   strengthens the result); the cycle already rules out efficient + BIC.

The key calculation: because b_1 does not enter v_1, agent 1's payoff from
misreporting b_1 depends ONLY on how the report changes the allocation x
(which affects whether agent 1 gets the object) and the transfer. Efficiency
makes x sensitive to b_1 (since b_1 enters v_2), but BIC requires agent 1 to
not exploit this. The 4-cycle exposes the inconsistency.

### Why this is faithful to the paper

- The paper's congruence condition IS an integrability (path-independence)
  condition; the 4-cycle is its discrete form.
- Multidimensionality is essential: with 1D types (just a_i), the cycle
  collapses and AGV-style possibility returns.
- Interdependence is essential: if b_i entered no one's value, the signal
  would be irrelevant and the cycle would be vacuous.

### Deliverables

- `JM/Defs.lean`: types, values, welfare, xmax, interim utility, IsEfficient,
  IsBIC, IsBudgetBalanced (reuse AGV patterns with interdependent values).
- `JM/Impossibility.lean`: the cycle lemma + main impossibility theorem.
- Comparator: `JM.jehiel_moldovanu_impossibility` (+ supporting lemmas).
- Axioms ⊆ {propext, Classical.choice, Quot.sound}; zero sorries.

## Prior art

Palomar registry search performed 2026-10-02 for "jehiel", "moldovanu",
"interdependent valuations", "multidimensional": zero results on all four
queries. (Sanity check: "mechanism design" returns 1 result, Arthur's
revenue-equivalence-lean, confirming the registry has mechanism-design
content but nothing Jehiel-Moldovanu-related.) This records only that dated
registry search.

## M1 findings (2026-10-02)

- `JM/Defs.lean` written (Codex) and verified to build green (`lake build`,
  3000 jobs, exit 0; only the intended theorem-level `sorry` plus a
  deprecated-import warning). Concrete parameters fixed:
  - `valA(true) = 1` (gap 1), `valB(true) = 2` (gap 2), coefficient `c = 1`.
  - Agent i's value when winning: `a_i + b_{other(i)}` (loser gets 0).
  - `interimUtil` evaluates value at the true profile, allocation/payment at
    the reported profile (AGV pattern adapted).
- The useful cycle is the REVERSE of the M0 proposal:
  `(F,F) -> (F,T) -> (T,T) -> (T,F) -> (F,F)` (indexed cyclically by `Fin 4`).
- Efficiency ties occur at exactly 4 diagonal profiles
  `(t, t)` for `t` in `(F,F), (F,T), (T,T), (T,F)` (equal winning values);
  all other profiles have a forced winner.
- `scripts/verify_cycle.py` (written independently, not by Codex) enumerates
  all 2^4 = 16 efficient tie-breaking rules and confirms:
  `S_0 + S_1 = -1/2` for EVERY efficient rule, where `S_i` is agent i's
  value-only truthful-minus-deviation cycle sum under uniform priors.
- Proof plan (M2-M4): BIC gives `S_i(p) >= 0` per agent (each cycle term is a
  truthful-vs-deviation comparison); transfer terms telescope around the
  closed cycle (cyclic reindexing), so `S_i(p) = S_i(0)`; the computation
  gives `S_0(0) + S_1(0) = -1/2 < 0`, contradiction. In Lean the last step
  is a 16-way case split on the diagonal ties plus `decide`/`norm_num`
  (all profile evaluations are concrete). Budget balance is a hypothesis but
  is not needed for the contradiction.
