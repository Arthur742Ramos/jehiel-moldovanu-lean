#!/usr/bin/env python3
"""Verify the Jehiel-Moldovanu finite-instance cycle computation.

Two agents, types Bool x Bool. Agent i type (a_i, b_i); a_i is own-value
signal, b_i affects the OTHER agent's value. valA(true)=1, valB(true)=2, c=1.

value(i, winner k, profile t) = a_i + b_{other(i)} if i == k else 0.

Cycle for each agent: (F,F) -> (F,T) -> (T,T) -> (T,F) -> (F,F)  (mod 4).

For an efficient allocation rule x (ties broken arbitrarily at profiles
where both agents have equal winning value), the value-only cycle sum
S_i = sum_j E_{t_-i}[ v_i(x(t^j,t_-i),(t^j,t_-i)) - v_i(x(t^{j+1},t_-i),(t^j,t_-i)) ]
must satisfy S_0 + S_1 = -1/2 for EVERY tie-breaking choice. By BIC with
telescoping transfers each S_i >= 0, giving the contradiction.
"""

from itertools import product

agents = [0, 1]
bools = [False, True]
types = list(product(bools, bools))          # 4 types per agent
profiles = list(product(types, types))       # 16 full profiles, (t0, t1)

def valA(a): return 1.0 if a else 0.0
def valB(b): return 2.0 if b else 0.0
c = 1.0

def other(i): return 1 - i

def value(i, k, t):
    """Interdependent value of agent i when winner is k at true profile t."""
    if i != k:
        return 0.0
    (a_i, b_i) = t[i]
    (a_j, b_j) = t[other(i)]
    return valA(a_i) + c * valB(b_j)

def welfare(t, k):
    return sum(value(i, k, t) for i in agents)

# cycle: (F,F) -> (F,T) -> (T,T) -> (T,F)
cycle = [(False, False), (False, True), (True, True), (True, False)]

def cycle_sum(x, i):
    """Value-only cycle sum for agent i under allocation rule x (zero transfers)."""
    total = 0.0
    for j in range(4):
        tj = cycle[j]
        tj1 = cycle[(j + 1) % 4]
        for t_opp in types:  # opponent type, uniform 1/4
            prof_truth = (tj, t_opp) if i == 0 else (t_opp, tj)
            prof_rep = (tj1, t_opp) if i == 0 else (t_opp, tj1)
            truth = value(i, x[prof_truth], prof_truth)
            dev = value(i, x[prof_rep], prof_truth)
            total += (truth - dev) / 4.0
    return total

# Classify profiles by the efficient set: strict winner or tie.
tied = []      # profiles where both agents have equal winning value
forced = {}    # profile -> winner forced by efficiency
for t in profiles:
    w0, w1 = welfare(t, 0), welfare(t, 1)
    if w0 > w1:
        forced[t] = 0
    elif w1 > w0:
        forced[t] = 1
    else:
        tied.append(t)

print(f"tied profiles: {len(tied)}")
for t in tied:
    print(f"  {t}: values = {welfare(t, 0)} each")

# Enumerate all 2^(#tied) efficient tie-breaking rules.
results = set()
worst = None
for bits in product([0, 1], repeat=len(tied)):
    x = dict(forced)
    for t, b in zip(tied, bits):
        x[t] = b
    s = cycle_sum(x, 0) + cycle_sum(x, 1)
    results.add(round(s, 12))
    if worst is None or s > worst[0]:
        worst = (s, bits)

print(f"\ndistinct values of S_0 + S_1 over all efficient rules: {sorted(results)}")
print(f"all equal to -1/2: {results == {-0.5}}")
print(f"max over rules (must be < 0 for contradiction): {worst[0]}")
assert results == {-0.5}, "CYCLE CONSTANT FAILED"
print("OK: every efficient rule gives total value-only cycle sum -1/2 < 0, "
      "while BIC forces each agent's cycle sum >= 0.")
