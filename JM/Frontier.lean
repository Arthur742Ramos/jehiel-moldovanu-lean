module

public import JM.Sharp

@[expose] public section

namespace JM.Sharp
noncomputable section

/-- Mechanisms meeting both an incentive-error and an expected-loss budget. -/
def Feasible (a b ε D : ℝ) : Prop :=
  ∃ q : RandomAllocation, ∃ p : Transfers,
    IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p ε ∧ loss a b q ≤ D

/-- Exact BIC has a positive, sharp welfare cost, even allowing lotteries. -/
theorem exact_bic_loss (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (q : RandomAllocation) (p : Transfers) (hq : IsLottery q)
    (hbic : ApproxBIC a b q p 0) : (b-a)/16 ≤ loss a b q := by
  have hf := welfare_incentive_frontier a b ha hab q p 0 hq hbic
  nlinarith

/-- Exact BIC and budget balance attain the minimum welfare loss. -/
theorem exact_bic_attained (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ q : RandomAllocation, ∃ p : Transfers,
      IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p 0 ∧ loss a b q = (b-a)/16 := by
  obtain ⟨q,p,hq,hp,hb,hd,_⟩ := frontier_attained a b ha hab 1 (by norm_num) (by norm_num)
  refine ⟨q,p,hq,hp,?_,?_⟩
  · simpa using hb
  · simpa using hd

/-- Complete feasibility characterization for nonnegative error/loss budgets.
This quantifies over all mechanisms in one direction and constructs a
budget-balanced mechanism in the other direction. -/
theorem feasible_iff (a b ε D : ℝ) (ha : 0 < a) (hab : a < b)
    (hε : 0 ≤ ε) (hD : 0 ≤ D) :
    Feasible a b ε D ↔ a*(b-a)/8 ≤ (b-a)*ε + 2*a*D := by
  constructor
  · rintro ⟨q,p,hq,_,hb,hd⟩
    have hf := welfare_incentive_frontier a b ha hab q p ε hq hb
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*a)
    linarith
  · intro hf
    by_cases hlarge : a/8 ≤ ε
    · refine ⟨frontierLottery 0, frontierTransfers a b 0,
        frontier_lottery 0 (by norm_num) (by norm_num), frontier_budget a b 0, ?_, ?_⟩
      · have hb := frontier_bic a b ha 0 (by norm_num) (by norm_num)
        intro i s r
        have hi := hb i s r
        simp only [sub_zero, mul_one] at hi
        linarith
      · rw [frontier_loss a b ha hab]
        simpa using hD
    · let θ : ℝ := (a-8*ε)/a
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (le_of_lt ha)
      have hθ1 : θ ≤ 1 := (div_le_one ha).mpr (by linarith)
      have herror : a*(1-θ)/8 = ε := by dsimp [θ]; field_simp; ring
      refine ⟨frontierLottery θ, frontierTransfers a b θ,
        frontier_lottery θ hθ0 hθ1, frontier_budget a b θ, ?_, ?_⟩
      · rw [← herror]
        exact frontier_bic a b ha θ hθ0 hθ1
      · rw [frontier_loss a b ha hab]
        have hid : 2*a*((b-a)*θ/16) = a*(b-a)/8-(b-a)*ε := by
          dsimp [θ]; field_simp; ring
        have hh : 2*a*((b-a)*θ/16) ≤ 2*a*D := by rw [hid]; linarith
        nlinarith

end
end JM.Sharp
