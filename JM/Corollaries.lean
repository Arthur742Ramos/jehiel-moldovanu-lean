module

public import JM.Frontier

@[expose] public section

namespace JM
open scoped BigOperators
noncomputable section

/-- Embed a deterministic allocation as a Bernoulli lottery. -/
def deterministicLottery (x : Allocation) (t : Profile) : ℝ := if x t = 0 then 1 else 0

/-- The deterministic embedding is a valid lottery. -/
theorem deterministic_lottery (x : Allocation) : Sharp.IsLottery (deterministicLottery x) := by
  intro t
  unfold deterministicLottery
  split_ifs <;> norm_num

/-- At a=1,b=2, the randomized utility definition agrees with the old model. -/
theorem deterministic_utility (x : Allocation) (p : Transfers) (i : Agent)
    (s r : Bool × Bool) :
    Sharp.utility 1 2 (deterministicLottery x) p i s r = interimUtil uniformPrior x p i s r := by
  have hv (j : Agent) (k : X) (t : Profile) : Sharp.payoff 1 2 j k t = value j k t := by
    unfold Sharp.payoff Sharp.winningValue value valA valB c
    split_ifs <;> norm_num
  have he (t u : Profile) (j : Agent) :
      deterministicLottery x t * value j 0 u + (1-deterministicLottery x t) * value j 1 u =
      value j (x t) u := by
    rcases alternative_cases (x t) with h | h
    · simp [deterministicLottery, h]
    · simp [deterministicLottery, h]
  fin_cases i
  · change Sharp.utility 1 2 (deterministicLottery x) p 0 s r = interimUtil uniformPrior x p 0 s r
    rw [interimUtil_zero]
    simp only [Sharp.utility, Sharp.expectedValue, Sharp.reports, ↓reduceIte, hv]
    simp_rw [he]
  · change Sharp.utility 1 2 (deterministicLottery x) p 1 s r = interimUtil uniformPrior x p 1 s r
    rw [interimUtil_one]
    simp only [Sharp.utility, Sharp.expectedValue, Sharp.reports, n10, ↓reduceIte, hv]
    simp_rw [he]

/-- Efficiency gives zero expected loss in the deterministic embedding. -/
theorem deterministic_loss (x : Allocation) (hx : IsEfficient x) :
    Sharp.loss 1 2 (deterministicLottery x) = 0 := by
  have hv (k : X) (t : Profile) : Sharp.socialWelfare 1 2 t k = welfare t k := by
    unfold Sharp.socialWelfare welfare
    apply Finset.sum_congr rfl
    intro j _
    unfold Sharp.payoff Sharp.winningValue value valA valB c
    split_ifs <;> norm_num
  unfold Sharp.loss Sharp.expectedWelfare
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro o _
  simp only [hv]
  rcases alternative_cases (x (![s,o] : Profile)) with h | h
  · have hm := hx (![s,o] : Profile) 1
    rw [h] at hm
    simp [deterministicLottery, h, max_eq_left hm]
  · have hm := hx (![s,o] : Profile) 0
    rw [h] at hm
    simp [deterministicLottery, h, max_eq_right hm]

/-- The old selected theorem follows from the parametric randomized frontier.
Budget balance is retained in the old contract but unnecessary for necessity. -/
theorem jehiel_moldovanu_impossibility :
    ∀ (x : Allocation) (p : Transfers),
      IsEfficient x → IsBIC uniformPrior x p → IsBudgetBalanced p → False := by
  intro x p he hb _
  have hBIC : Sharp.ApproxBIC 1 2 (deterministicLottery x) p 0 := by
    intro i s r
    simp only [deterministic_utility, add_zero]
    exact hb i s r
  have hf := Sharp.welfare_incentive_frontier 1 2 (by norm_num) (by norm_num)
    (deterministicLottery x) p 0 (deterministic_lottery x) hBIC
  rw [deterministic_loss x he] at hf
  norm_num at hf

end
end JM
