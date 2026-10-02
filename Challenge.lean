module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

/-! Continuous binary coefficient congruence and explicit-transfer implementation,
with an independent uniform-square auction impossibility for all a,b>0.
The earlier sharp finite welfare/incentive frontier is separately retained.
Genuine definitions are repeated verbatim; only selected theorem proofs are holes.
No full arbitrary-alternative theorem, novelty or hosted verdict is claimed. -/

@[expose] public section

namespace JM
open scoped BigOperators NNReal
noncomputable section

abbrev Agent := Fin 2

abbrev X := Fin 2

abbrev T (_i : Agent) := Bool × Bool

abbrev Profile := (i : Agent) → T i

abbrev Allocation := Profile → X

abbrev Transfers := Agent → Profile → ℝ

def valA (a : Bool) : ℝ := if a then 1 else 0

def valB (b : Bool) : ℝ := if b then 2 else 0

def c : ℝ := 1

def other (i : Agent) : Agent := if i = 0 then 1 else 0

def value (i : Agent) (k : X) (t : Profile) : ℝ :=
  if i = k then valA (t i).1 + c * valB (t (other i)).2 else 0

def welfare (t : Profile) (k : X) : ℝ := ∑ i, value i k t

theorem argmax_nonempty (t : Profile) :
    ∃ k : X, ∀ y : X, welfare t y ≤ welfare t k := by
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image
    (Finset.univ : Finset X) (welfare t)
    ⟨0, Finset.mem_univ _⟩
  exact ⟨k, fun y => hk y (Finset.mem_univ y)⟩

def xmax (t : Profile) : X :=
  (Classical.choice (show Nonempty {k : X // ∀ y : X, welfare t y ≤ welfare t k} from by
    obtain ⟨k, hk⟩ := argmax_nonempty t
    exact ⟨⟨k, hk⟩⟩)).val

variable (π : (i : Agent) → PMF (T i))

def weight (t : Profile) : ℝ :=
  ∏ i, (((π i (t i)).toNNReal : ℝ≥0) : ℝ)

def splice (i : Agent) (s : T i) (t : Profile) : Profile :=
  Function.update t i s

@[simp] theorem splice_self (i : Agent) (s : T i) (t : Profile) :
    splice i s t i = s := Function.update_self i s t

def interimUtil (x : Allocation) (p : Transfers)
    (i : Agent) (s r : T i) : ℝ :=
  ∑ t : Profile, weight π t *
    (value i (x (splice i r t)) (splice i s t) + p i (splice i r t))

def IsEfficient (x : Allocation) : Prop :=
  ∀ t y, welfare t y ≤ welfare t (x t)

def IsBIC (x : Allocation) (p : Transfers) : Prop :=
  ∀ i (s r : T i), interimUtil π x p i s r ≤ interimUtil π x p i s s

def IsBudgetBalanced (p : Transfers) : Prop :=
  ∀ t, ∑ i, p i t = 0

def uniformPrior : (i : Agent) → PMF (T i) :=
  fun i => PMF.uniformOfFintype (T i)

def cycleType (j : Fin 4) : Bool × Bool :=
  if j = 0 then (false, false)
  else if j = 1 then (false, true)
  else if j = 2 then (true, true)
  else (true, false)

def cycleSum (x : Allocation) (i : Agent) : ℝ :=
  ∑ j : Fin 4,
    (interimUtil π x (fun _ _ => 0) i (cycleType j) (cycleType j) -
      interimUtil π x (fun _ _ => 0) i (cycleType j) (cycleType (j + 1)))

end
end JM

namespace JM.Quantitative
open scoped BigOperators NNReal
noncomputable section

variable {T O K : Type*} [Fintype T] [Fintype O] [Fintype K]

abbrev Lottery (T O K : Type*) := T → O → K → ℝ

def utility (ν : O → ℝ) (v : T → O → K → ℝ)
    (q : Lottery T O K) (p : T → O → ℝ) (s r : T) : ℝ :=
  ∑ o, ν o * ((∑ k, q r o k * v s o k) + p r o)

def ApproxBIC (ν : O → ℝ) (v : T → O → K → ℝ)
    (q : Lottery T O K) (p : T → O → ℝ) (ε : ℝ) : Prop :=
  ∀ s r, utility ν v q p s r ≤ utility ν v q p s s + ε

def Balanced (ell : T → T → ℝ) : Prop :=
  ∀ r, (∑ s, ell r s) = ∑ s, ell s r

def flowMass (ell : T → T → ℝ) : ℝ := ∑ s, ∑ r, ell s r

def coefficient (v : T → O → K → ℝ) (ell : T → T → ℝ)
    (r : T) (o : O) (k : K) : ℝ :=
  ∑ s, (ell r s * v r o k - ell s r * v s o k)

def welfareLoss (α : T → ℝ) (ν : O → ℝ) (W : T → O → K → ℝ)
    (g : T → O → ℝ) (q : Lottery T O K) : ℝ :=
  ∑ r, ∑ o, α r * ν o * (g r o - ∑ k, q r o k * W r o k)

theorem welfare_incentive_bound
    (α : T → ℝ) (ν : O → ℝ) (v W : T → O → K → ℝ)
    (g : T → O → ℝ) (q : Lottery T O K) (p : T → O → ℝ)
    (ell : T → T → ℝ) (a β ε : ℝ)
    (hα : ∑ r, α r = 1) (hν : ∑ o, ν o = 1)
    (hν0 : ∀ o, 0 ≤ ν o) (hq0 : ∀ r o k, 0 ≤ q r o k)
    (hq1 : ∀ r o, ∑ k, q r o k = 1)
    (hell0 : ∀ s r, 0 ≤ ell s r) (hell : Balanced ell)
    (hBIC : ApproxBIC ν v q p ε)
    (hcert : ∀ r o k, coefficient v ell r o k ≤
      α r * (β * (g r o - W r o k) - a)) :
    a ≤ β * welfareLoss α ν W g q + flowMass ell * ε := by
  sorry

end
end JM.Quantitative

namespace JM.Sharp
open scoped BigOperators NNReal
noncomputable section

def winningValue (a b : ℝ) (i : Agent) (t : Profile) : ℝ :=
  a * (if (t i).1 then 1 else 0) + b * (if (t (other i)).2 then 1 else 0)

def payoff (a b : ℝ) (i : Agent) (k : X) (t : Profile) : ℝ :=
  if i = k then winningValue a b i t else 0

def socialWelfare (a b : ℝ) (t : Profile) (k : X) : ℝ := ∑ i, payoff a b i k t

abbrev RandomAllocation := Profile → ℝ

def IsLottery (q : RandomAllocation) : Prop := ∀ t, 0 ≤ q t ∧ q t ≤ 1

def reports (i : Agent) (s o : Bool × Bool) : Profile :=
  if i = 0 then ![s, o] else ![o, s]

def expectedValue (a b : ℝ) (q : RandomAllocation) (i : Agent) (s r o : Bool × Bool) : ℝ :=
  q (reports i r o) * payoff a b i 0 (reports i s o) +
    (1 - q (reports i r o)) * payoff a b i 1 (reports i s o)

def utility (a b : ℝ) (q : RandomAllocation) (p : Transfers)
    (i : Agent) (s r : Bool × Bool) : ℝ :=
  ∑ o : Bool × Bool, (1 / 4 : ℝ) * (expectedValue a b q i s r o + p i (reports i r o))

def ApproxBIC (a b : ℝ) (q : RandomAllocation) (p : Transfers) (ε : ℝ) : Prop :=
  ∀ i s r, utility a b q p i s r ≤ utility a b q p i s s + ε

def expectedWelfare (a b : ℝ) (q : RandomAllocation) (t : Profile) : ℝ :=
  q t * socialWelfare a b t 0 + (1 - q t) * socialWelfare a b t 1

def loss (a b : ℝ) (q : RandomAllocation) : ℝ :=
  ∑ s : Bool × Bool, ∑ o : Bool × Bool, (1 / 16 : ℝ) *
    (max (socialWelfare a b ![s, o] 0) (socialWelfare a b ![s, o] 1) - expectedWelfare a b q ![s, o])

def canonicalProbability (t : Profile) : ℝ :=
  if welfare t 1 < welfare t 0 then 1
  else if welfare t 0 < welfare t 1 then 0 else 1 / 2

def twoCycle (a b : ℝ) (q : RandomAllocation) (i : Agent) : ℝ :=
  utility a b q (fun _ _ => 0) i (false, false) (false, false) -
  utility a b q (fun _ _ => 0) i (false, false) (true, true) +
  utility a b q (fun _ _ => 0) i (true, true) (true, true) -
  utility a b q (fun _ _ => 0) i (true, true) (false, false)

def score (a _b : ℝ) (s : Bool × Bool) : ℝ :=
  if s = (true, true) then a / 4 else if s = (false, false) then -a / 4 else 0

def cycleCoefficient (a b : ℝ) (s o : Bool × Bool) : ℝ := score a b s - score a b o

theorem welfare_incentive_frontier (a b : ℝ) (ha : 0 < a) (hab : a < b) (q : RandomAllocation) (p : Transfers) (ε : ℝ)
    (hq : IsLottery q) (h : ApproxBIC a b q p ε) :
    a*(b-a)/8 ≤ (b-a)*ε + 2*a * loss a b q := by
  sorry

def frontierLottery (θ : ℝ) (t : Profile) : ℝ :=
  if t 0 = (false,false) ∧ t 1 = (true,true) then 1 - θ / 2
  else if t 0 = (true,true) ∧ t 1 = (false,false) then θ / 2
  else canonicalProbability t

def potential (a b : ℝ) (θ : ℝ) (s : Bool × Bool) : ℝ :=
  if s = (false,false) then -b/2 + b*θ/8
  else if s = (false,true) then -b/8
  else if s = (true,false) then -3*a/8-b/2
  else a*(1-θ)/8-3*b/8

def frontierTransfers (a b : ℝ) (θ : ℝ) (i : Agent) (t : Profile) : ℝ :=
  potential a b θ (t i) - potential a b θ (t (other i))

theorem frontier_attained (a b : ℝ) (ha : 0 < a) (hab : a < b) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∃ q : RandomAllocation, ∃ p : Transfers,
      IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p (a*(1-θ)/8) ∧
      loss a b q = (b-a)*θ/16 ∧ ((b-a)*(a*(1-θ)/8) + 2*a * loss a b q = a*(b-a)/8) := by
  sorry

end
end JM.Sharp

namespace JM.Sharp
open scoped BigOperators NNReal
noncomputable section

def Feasible (a b ε D : ℝ) : Prop :=
  ∃ q : RandomAllocation, ∃ p : Transfers,
    IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p ε ∧ loss a b q ≤ D

theorem exact_bic_loss (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (q : RandomAllocation) (p : Transfers) (hq : IsLottery q)
    (hbic : ApproxBIC a b q p 0) : (b-a)/16 ≤ loss a b q := by
  sorry

theorem exact_bic_attained (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ q : RandomAllocation, ∃ p : Transfers,
      IsLottery q ∧ IsBudgetBalanced p ∧ ApproxBIC a b q p 0 ∧ loss a b q = (b-a)/16 := by
  sorry

theorem feasible_iff (a b ε D : ℝ) (ha : 0 < a) (hab : a < b)
    (hε : 0 ≤ ε) (hD : 0 ≤ D) :
    Feasible a b ε D ↔ a*(b-a)/8 ≤ (b-a)*ε + 2*a*D := by
  sorry

end
end JM.Sharp

namespace JM
open scoped BigOperators NNReal
noncomputable section

def deterministicLottery (x : Allocation) (t : Profile) : ℝ := if x t = 0 then 1 else 0

theorem jehiel_moldovanu_impossibility :
    ∀ (x : Allocation) (p : Transfers),
      IsEfficient x → IsBIC uniformPrior x p → IsBudgetBalanced p → False := by
  sorry

end
end JM

namespace JM.Binary
open scoped BigOperators NNReal
noncomputable section

open MeasureTheory
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω]

def EfficientAt (q W : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ (0 < W → q = 1) ∧ (W < 0 → q = 0)

def utility (μ : Measure Ω) {U : Set E} (c : E →ₗ[ℝ] ℝ)
    (g : U → Ω → ℝ) (d : Ω → ℝ) (q p : U → Ω → ℝ) (t r : U) : ℝ :=
  ∫ o, g t o + q r o * (c t.val + d o) + p r o ∂μ

def Lottery {U : Set E} (q : U → Ω → ℝ) : Prop :=
  (∀ r, Measurable (q r)) ∧ ∀ r o, 0 ≤ q r o ∧ q r o ≤ 1

def Transfers (μ : Measure Ω) {U : Set E} (p : U → Ω → ℝ) : Prop :=
  ∀ r, Integrable (p r) μ

def BIC (μ : Measure Ω) {U : Set E} (c : E →ₗ[ℝ] ℝ)
    (g : U → Ω → ℝ) (d : Ω → ℝ) (q p : U → Ω → ℝ) : Prop :=
  ∀ t r, utility μ c g d q p t r ≤ utility μ c g d q p t t

def Efficient {U : Set E} (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ)
    (q : U → Ω → ℝ) : Prop := ∀ r o, EfficientAt (q r o) (A r.val + H o)

def Active (μ : Measure Ω) (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ) (t0 : E) : Prop :=
  ∀ η : ℝ, 0 < η → μ {o | |A t0 + H o| < η} ≠ 0

def probability (μ : Measure Ω) {U : Set E} (q : U → Ω → ℝ) (r : U) : ℝ :=
  ∫ o, q r o ∂μ

theorem utility_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (t r : U) :
    Integrable (fun o => g t o + q r o * (c t.val + d o) + p r o) μ := by
  sorry

theorem congruence (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (hb : BIC μ c g d q p)
    (he : Efficient A H q) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) : ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  sorry

def alignedTransfers {U : Set E} (lam : ℝ) (d H : Ω → ℝ) (q : U → Ω → ℝ) :
    U → Ω → ℝ := fun r o => (lam * H o - d o) * q r o

def ExPostIC {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    (q p : U → Ω → ℝ) : Prop := ∀ t r o,
  g t o + q r o * (c t.val + d o) + p r o ≤
  g t o + q t o * (c t.val + d o) + p t o

theorem aligned_ex_post (c A : E →ₗ[ℝ] ℝ) {U : Set E} (g : U → Ω → ℝ)
    (d H : Ω → ℝ) {q : U → Ω → ℝ} (hq : Lottery q) (he : Efficient A H q)
    (lam : ℝ) (hl : 0 ≤ lam) (hc : ∀ v, c v = lam * A v) :
    ExPostIC c g d q (alignedTransfers lam d H q) := by
  sorry

theorem implementation_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    {q : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hH : Integrable H μ) (hq : Lottery q) (he : Efficient A H q) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) :
    (∃ p : U → Ω → ℝ, Transfers μ p ∧ BIC μ c g d q p) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  sorry

def thresholdLottery {U : Set E} (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ) :
    U → Ω → ℝ := fun r o => if 0 < A r.val + H o then 1 else 0

theorem efficient_bic_exists_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hH : Integrable H μ) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) :
    (∃ q p : U → Ω → ℝ, Lottery q ∧ Transfers μ p ∧ Efficient A H q ∧
      BIC μ c g d q p) ↔ ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  sorry

end
end JM.Binary

namespace JM.ContinuousAuction
open scoped BigOperators NNReal
noncomputable section

open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace

def domain : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

abbrev Signal := domain
attribute [local instance] Measure.Subtype.measureSpace

def prior : Measure Signal := volume

def jointPrior : Measure (Signal × Signal) := prior.prod prior

def privateCoefficient (a : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ := a • LinearMap.fst ℝ ℝ ℝ

def socialCoefficient (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  a • LinearMap.fst ℝ ℝ ℝ - b • LinearMap.snd ℝ ℝ ℝ

def privateOpponent (b : ℝ) (o : Signal) : ℝ := b * o.val.2

def socialOpponent (a b : ℝ) (o : Signal) : ℝ := b * o.val.2 - a * o.val.1

def baseline : Signal → Signal → ℝ := fun _ _ => 0

def value (a b : ℝ) (agent winner : Bool) (t o : Signal) : ℝ :=
  if agent = winner then
    if agent then a * t.val.1 + b * o.val.2 else a * o.val.1 + b * t.val.2
  else 0

def welfare (a b : ℝ) (winner : Bool) (t o : Signal) : ℝ :=
  value a b true winner t o + value a b false winner t o

def Efficient (a b : ℝ) (q : Signal → Signal → ℝ) : Prop :=
  ∀ t o, Binary.EfficientAt (q t o) (welfare a b true t o - welfare a b false t o)

def utility (a b : ℝ) (q p : Signal → Signal → ℝ) (t r : Signal) : ℝ :=
  ∫ o, q r o * value a b true true t o +
    (1 - q r o) * value a b true false t o + p r o ∂prior

def Agent0BIC (a b : ℝ) (q p : Signal → Signal → ℝ) : Prop :=
  ∀ t r, utility a b q p t r ≤ utility a b q p t t

theorem uniform_probability : IsProbabilityMeasure (volume : Measure Signal) := by
  sorry

theorem prior_probability : IsProbabilityMeasure prior := by
  sorry

theorem joint_probability : IsProbabilityMeasure jointPrior := by
  sorry

def box (ρ : ℝ) : Set (ℝ × ℝ) :=
  Ioo ((1:ℝ)/2-ρ) (1/2+ρ) ×ˢ Ioo ((1:ℝ)/2-ρ) (1/2+ρ)

theorem welfare_difference (a b : ℝ) (t o : Signal) :
    welfare a b true t o - welfare a b false t o =
      socialCoefficient a b t.val + socialOpponent a b o := by
  sorry

theorem utility_integrable (a b : ℝ) (hb : 0 ≤ b) {q p : Signal → Signal → ℝ}
    (hq : Binary.Lottery q) (hp : Binary.Transfers prior p) (t r : Signal) :
    Integrable (fun o => q r o * value a b true true t o +
      (1 - q r o) * value a b true false t o + p r o) prior := by
  sorry

theorem impossibility (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (q p : Signal → Signal → ℝ) (hq : Binary.Lottery q)
    (hp : Binary.Transfers prior p) (he : Efficient a b q) (hB : Agent0BIC a b q p) :
    False := by
  sorry

end
end JM.ContinuousAuction
