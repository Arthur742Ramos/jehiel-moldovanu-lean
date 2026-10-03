module

public import JM.Defs
public import JM.Quantitative

@[expose] public section

/-! Sharp welfare/incentive frontier for the finite JM model.
Own-value gap a>0 and external-value gap b>a are arbitrary. A one-parameter,
ex-post budget-balanced mechanism attains every point of the frontier. -/
namespace JM.Sharp
open scoped BigOperators
noncomputable section

/-- Winning value for arbitrary own and external signal gaps. -/
def winningValue (a b : ℝ) (i : Agent) (t : Profile) : ℝ :=
  a * (if (t i).1 then 1 else 0) + b * (if (t (other i)).2 then 1 else 0)

/-- A nonrecipient has zero value. -/
def payoff (a b : ℝ) (i : Agent) (k : X) (t : Profile) : ℝ :=
  if i = k then winningValue a b i t else 0

/-- Social welfare for an allocation to a single recipient. -/
def socialWelfare (a b : ℝ) (t : Profile) (k : X) : ℝ := ∑ i, payoff a b i k t

/-- Probability that agent zero receives the object. -/
abbrev RandomAllocation := Profile → ℝ

/-- A valid lottery at every report profile. -/
def IsLottery (q : RandomAllocation) : Prop := ∀ t, 0 ≤ q t ∧ q t ≤ 1

/-- Put own and opposing reports in their appropriate positions. -/
def reports (i : Agent) (s o : Bool × Bool) : Profile :=
  if i = 0 then ![s, o] else ![o, s]

/-- Expected value at the true profile with a Bernoulli allocation. -/
def expectedValue (a b : ℝ) (q : RandomAllocation) (i : Agent) (s r o : Bool × Bool) : ℝ :=
  q (reports i r o) * payoff a b i 0 (reports i s o) +
    (1 - q (reports i r o)) * payoff a b i 1 (reports i s o)

/-- Uniform interim utility, for arbitrary randomized allocations. -/
def utility (a b : ℝ) (q : RandomAllocation) (p : Transfers)
    (i : Agent) (s r : Bool × Bool) : ℝ :=
  ∑ o : Bool × Bool, (1 / 4 : ℝ) * (expectedValue a b q i s r o + p i (reports i r o))

/-- Every deviation yields an interim utility gain at most `ε`. -/
def ApproxBIC (a b : ℝ) (q : RandomAllocation) (p : Transfers) (ε : ℝ) : Prop :=
  ∀ i s r, utility a b q p i s r ≤ utility a b q p i s s + ε

/-- Expected social welfare at a profile. -/
def expectedWelfare (a b : ℝ) (q : RandomAllocation) (t : Profile) : ℝ :=
  q t * socialWelfare a b t 0 + (1 - q t) * socialWelfare a b t 1

/-- Average loss from maximum possible welfare under independent uniform priors. -/
def loss (a b : ℝ) (q : RandomAllocation) : ℝ :=
  ∑ s : Bool × Bool, ∑ o : Bool × Bool, (1 / 16 : ℝ) *
    (max (socialWelfare a b ![s, o] 0) (socialWelfare a b ![s, o] 1) - expectedWelfare a b q ![s, o])

/-- A symmetric efficient lottery, splitting welfare ties equally. -/
def canonicalProbability (t : Profile) : ℝ :=
  if welfare t 1 < welfare t 0 then 1
  else if welfare t 0 < welfare t 1 then 0 else 1 / 2

/-- Two opposite deviations between the lowest and highest signals. -/
def twoCycle (a b : ℝ) (q : RandomAllocation) (i : Agent) : ℝ :=
  utility a b q (fun _ _ => 0) i (false, false) (false, false) -
  utility a b q (fun _ _ => 0) i (false, false) (true, true) +
  utility a b q (fun _ _ => 0) i (true, true) (true, true) -
  utility a b q (fun _ _ => 0) i (true, true) (false, false)

/-- The coefficient of a report's winning probability in the two-cycle. -/
def score (a _b : ℝ) (s : Bool × Bool) : ℝ :=
  if s = (true, true) then a / 4 else if s = (false, false) then -a / 4 else 0

/-- Combined coefficients from both agents' two-cycles. -/
def cycleCoefficient (a b : ℝ) (s o : Bool × Bool) : ℝ := score a b s - score a b o

/-- Approximate BIC bounds each two-cycle, independently of transfers. -/
theorem twoCycle_lower (a b : ℝ) (q : RandomAllocation) (p : Transfers) (ε : ℝ)
    (h : ApproxBIC a b q p ε) (i : Agent) : -2 * ε ≤ twoCycle a b q i := by
  have h0 := h i (false, false) (true, true)
  have h1 := h i (true, true) (false, false)
  have split (s r : Bool × Bool) :
      utility a b q p i s r = utility a b q (fun _ _ => 0) i s r +
        ∑ o : Bool × Bool, (1 / 4 : ℝ) * p i (reports i r o) := by
    simp [utility, mul_add, Finset.sum_add_distrib]
  simp_rw [split] at h0 h1
  unfold twoCycle
  linarith

/-- The combined cycle is a linear functional of the sixteen probabilities. -/
theorem twoCycle_pair (a b : ℝ) (q : RandomAllocation) :
    twoCycle a b q 0 + twoCycle a b q 1 =
      ∑ s : Bool × Bool, ∑ o : Bool × Bool, cycleCoefficient a b s o * q ![s, o] := by
  norm_num [twoCycle, utility, expectedValue, reports, Fintype.sum_prod_type,
    Fintype.sum_bool, cycleCoefficient, score, payoff, winningValue, socialWelfare, value, valA, valB, c, other,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Pointwise dual certificate: cycle improvement costs expected welfare. -/
theorem pointwise_certificate (a b : ℝ) (ha : 0 < a) (hab : a < b) (s o : Bool × Bool) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (b-a) * (cycleCoefficient a b s o * z) ≤
      (b-a) * (cycleCoefficient a b s o * canonicalProbability ![s, o]) +
        (a / 2 : ℝ) * (max (socialWelfare a b ![s, o] 0) (socialWelfare a b ![s, o] 1) -
          (z * socialWelfare a b ![s, o] 0 + (1 - z) * socialWelfare a b ![s, o] 1)) := by
  let f (x : ℝ) := (b-a) * (cycleCoefficient a b s o * canonicalProbability ![s,o]) +
    (a/2) * (max (socialWelfare a b ![s,o] 0) (socialWelfare a b ![s,o] 1) -
      (x * socialWelfare a b ![s,o] 0 + (1-x) * socialWelfare a b ![s,o] 1)) -
    (b-a) * (cycleCoefficient a b s o * x)
  have endpoints : 0 ≤ f 0 ∧ 0 ≤ f 1 := by
    rcases s with ⟨u,v⟩; rcases o with ⟨d,e⟩
    cases u <;> cases v <;> cases d <;> cases e <;>
      norm_num [f, cycleCoefficient, score, canonicalProbability, welfare,
        Fin.sum_univ_two, payoff, winningValue, socialWelfare, value, valA, valB,
        c, other, Matrix.cons_val_zero, Matrix.cons_val_one, max_def] <;>
      split_ifs <;> constructor <;> nlinarith
  have affine : f z = (1-z) * f 0 + z * f 1 := by dsimp [f]; ring
  have hf : 0 ≤ f z := by
    rw [affine]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hz1) endpoints.1)
      (mul_nonneg hz0 endpoints.2)
  dsimp [f] at hf
  linarith

/-- The dual certificate bounds the combined cycle by welfare loss. -/
theorem cycle_loss_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (q : RandomAllocation) (hq : IsLottery q) :
    (b-a) * (twoCycle a b q 0 + twoCycle a b q 1) ≤ -a*(b-a) / 2 + 8*a * loss a b q := by
  rw [twoCycle_pair]
  simp only [Finset.mul_sum]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun o _ =>
      pointwise_certificate a b ha hab s o (q ![s,o]) (hq ![s,o]).1 (hq ![s,o]).2))
  have hc : (∑ s : Bool × Bool, ∑ o : Bool × Bool,
      (b-a) * (cycleCoefficient a b s o * canonicalProbability ![s,o])) = -a*(b-a) / 2 := by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, cycleCoefficient, score,
      canonicalProbability, welfare, Fin.sum_univ_two, payoff, winningValue, socialWelfare, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [Finset.sum_add_distrib] at hh
  rw [hc] at hh
  have he : (∑ s : Bool × Bool, ∑ o : Bool × Bool,
      (a / 2 : ℝ) * (max (socialWelfare a b ![s,o] 0) (socialWelfare a b ![s,o] 1) -
        (q ![s,o] * socialWelfare a b ![s,o] 0 + (1-q ![s,o]) * socialWelfare a b ![s,o] 1))) =
      8*a * loss a b q := by
    simp only [loss, expectedWelfare, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro o _
    ring
  rw [he] at hh
  exact hh

/-- Sharp universal lower bound, with no budget restriction on transfers. -/
theorem welfare_incentive_frontier (a b : ℝ) (ha : 0 < a) (hab : a < b) (q : RandomAllocation) (p : Transfers) (ε : ℝ)
    (hq : IsLottery q) (h : ApproxBIC a b q p ε) :
    a*(b-a)/8 ≤ (b-a)*ε + 2*a * loss a b q := by
  have h0 := twoCycle_lower a b q p ε h 0
  have h1 := twoCycle_lower a b q p ε h 1
  have hu := cycle_loss_bound a b ha hab q hq
  have hl := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (le_of_lt (sub_pos.mpr hab))
  nlinarith

/-- Frontier lottery: relax efficiency only at the two crossing profiles. -/
def frontierLottery (θ : ℝ) (t : Profile) : ℝ :=
  if t 0 = (false,false) ∧ t 1 = (true,true) then 1 - θ / 2
  else if t 0 = (true,true) ∧ t 1 = (false,false) then θ / 2
  else canonicalProbability t

/-- Report-only transfer potential, used for both agents. -/
def potential (a b : ℝ) (θ : ℝ) (s : Bool × Bool) : ℝ :=
  if s = (false,false) then -b/2 + b*θ/8
  else if s = (false,true) then -b/8
  else if s = (true,false) then -3*a/8-b/2
  else a*(1-θ)/8-3*b/8

/-- Antisymmetric transfers are exactly budget balanced at every profile. -/
def frontierTransfers (a b : ℝ) (θ : ℝ) (i : Agent) (t : Profile) : ℝ :=
  potential a b θ (t i) - potential a b θ (t (other i))

/-- The frontier probabilities are valid on the whole unit interval. -/
theorem frontier_lottery (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    IsLottery (frontierLottery θ) := by
  intro t
  unfold frontierLottery
  split_ifs
  · constructor <;> linarith
  · constructor <;> linarith
  · unfold canonicalProbability
    split_ifs <;> norm_num

/-- Exact welfare loss along the frontier. -/
theorem frontier_loss (a b : ℝ) (ha : 0 < a) (hab : a < b) (θ : ℝ) : loss a b (frontierLottery θ) = (b-a)*θ / 16 := by
  norm_num [loss, expectedWelfare, frontierLottery, canonicalProbability,
    Fintype.sum_prod_type, Fintype.sum_bool, welfare, Fin.sum_univ_two,
    payoff, winningValue, socialWelfare, value, valA, valB, c, other, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hab0 : 0 ≤ a + b := by linarith
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := by linarith
  have hab1 : a ≤ b := le_of_lt hab
  have haa : a ≤ a+b := by linarith
  have hbb : b ≤ a+b := by linarith
  simp only [max_eq_right haa, max_eq_left haa, max_eq_right hbb, max_eq_left hbb,
    max_eq_right hab1, max_eq_left hab1, max_eq_right ha0, max_eq_left ha0,
    max_eq_right hb0, max_eq_left hb0, max_eq_right hab0, max_eq_left hab0]
  ring

set_option maxHeartbeats 1200000 in
/-- The attaining mechanism satisfies all thirty-two incentive inequalities. -/
theorem frontier_bic (a b : ℝ) (ha : 0 < a) (θ : ℝ) (_h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ApproxBIC a b (frontierLottery θ) (frontierTransfers a b θ) (a*(1 - θ) / 8) := by
  have he : 0 ≤ a*(1-θ) := mul_nonneg (le_of_lt ha) (by linarith)
  have hf : 0 ≤ a*(4-θ) := mul_nonneg (le_of_lt ha) (by linarith)
  intro i s r
  fin_cases i <;> rcases s with ⟨u,v⟩ <;> rcases r with ⟨d,e⟩ <;>
    cases u <;> cases v <;> cases d <;> cases e <;>
    norm_num [utility, expectedValue, reports, frontierLottery, frontierTransfers,
      potential, canonicalProbability, Fintype.sum_prod_type, Fintype.sum_bool,
      welfare, Fin.sum_univ_two, payoff, winningValue, socialWelfare, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> nlinarith

/-- Budget balance holds at every report profile. -/
theorem frontier_budget (a b : ℝ) (θ : ℝ) : IsBudgetBalanced (frontierTransfers a b θ) := by
  intro t
  simp [frontierTransfers, Fin.sum_univ_two, other]
  ring

/-- Every point of the lower frontier is attained, even with budget balance. -/
theorem frontier_attained (a b : ℝ) (ha : 0 < a) (hab : a < b) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∃ q : RandomAllocation, ∃ p : Transfers,
      IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p (a*(1-θ)/8) ∧
      loss a b q = (b-a)*θ/16 ∧ ((b-a)*(a*(1-θ)/8) + 2*a * loss a b q = a*(b-a)/8) := by
  refine ⟨frontierLottery θ, frontierTransfers a b θ, frontier_lottery θ h0 h1,
    frontier_budget a b θ, frontier_bic a b ha θ h0 h1, frontier_loss a b ha hab θ, ?_⟩
  rw [frontier_loss a b ha hab]
  ring

end
end JM.Sharp
