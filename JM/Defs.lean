module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A finite Jehiel–Moldovanu impossibility instance

Two agents have independent two-dimensional binary types. The first signal
affects the agent's own value; the second affects the other agent's value.
The concrete signal values are `A = (0, 1)`, `B = (0, 2)`, with coefficient
`c = 1`. General independent priors are used in the utility definitions;
the impossibility statement specializes to uniform priors.

The useful cycle is `(false,false) → (false,true) → (true,true) →
(true,false) → (false,false)`, the reverse of the initial M0 proposal.
For every efficient rule, the two agents' value-only cycle sums together
equal `-1/2` under uniform priors (enumerated in `scripts/verify_cycle.py`).
One agent's cycle alone need not be negative because efficiency permits
arbitrary choices at ties. This is a finite instance, not the continuous
generic impossibility theorem of the original paper.
-/

namespace JM

open scoped BigOperators NNReal

noncomputable section

/-- There are two agents. -/
abbrev Agent := Fin 2

/-- Alternative `i` assigns the object to agent `i`. -/
abbrev X := Fin 2

/-- The value signal and the influence signal of an agent. -/
abbrev T (_i : Agent) := Bool × Bool

/-- A complete type (or report) profile. -/
abbrev Profile := (i : Agent) → T i

/-- A deterministic direct allocation rule. -/
abbrev Allocation := Profile → X

/-- Transfers received by agents; positive transfers increase utility. -/
abbrev Transfers := Agent → Profile → ℝ

/-- Own value signal, with strictly positive gap one. -/
def valA (a : Bool) : ℝ := if a then 1 else 0

/-- Influence signal, with strictly positive gap two. -/
def valB (b : Bool) : ℝ := if b then 2 else 0

/-- Positive coefficient on the other agent's influence signal. -/
def c : ℝ := 1

/-- The other agent in the two-agent population. -/
def other (i : Agent) : Agent := if i = 0 then 1 else 0

/-- Interdependent value at the true profile; a nonrecipient has value zero. -/
def value (i : Agent) (k : X) (t : Profile) : ℝ :=
  if i = k then valA (t i).1 + c * valB (t (other i)).2 else 0

/-- Total welfare at a type profile and an alternative. -/
def welfare (t : Profile) (k : X) : ℝ := ∑ i, value i k t

/-- Welfare attains a maximum on the finite nonempty alternative set. -/
theorem argmax_nonempty (t : Profile) :
    ∃ k : X, ∀ y : X, welfare t y ≤ welfare t k := by
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image
    (Finset.univ : Finset X) (welfare t)
    ⟨0, Finset.mem_univ _⟩
  exact ⟨k, fun y => hk y (Finset.mem_univ y)⟩

/-- An arbitrary welfare maximizer. Efficiency does not fix its tie choices. -/
def xmax (t : Profile) : X :=
  (Classical.choice (show Nonempty {k : X // ∀ y : X, welfare t y ≤ welfare t k} from by
    obtain ⟨k, hk⟩ := argmax_nonempty t
    exact ⟨⟨k, hk⟩⟩)).val

/-- Every alternative has welfare at most that of `xmax`. -/
theorem xmax_optimal (t : Profile) (k : X) :
    welfare t k ≤ welfare t (xmax t) := by
  have hmax : Nonempty {y : X // ∀ z : X, welfare t z ≤ welfare t y} := by
    obtain ⟨y, hy⟩ := argmax_nonempty t
    exact ⟨⟨y, hy⟩⟩
  exact (Classical.choice hmax).property k

variable (π : (i : Agent) → PMF (T i))

/-- Joint real probability weight under independent priors. -/
def weight (t : Profile) : ℝ :=
  ∏ i, (((π i (t i)).toNNReal : ℝ≥0) : ℝ)

/-- Replace an agent's component in a type or report profile. -/
def splice (i : Agent) (s : T i) (t : Profile) : Profile :=
  Function.update t i s

@[simp] theorem splice_self (i : Agent) (s : T i) (t : Profile) :
    splice i s t i = s := Function.update_self i s t

theorem splice_of_ne (i j : Agent) (s : T i) (t : Profile) (h : j ≠ i) :
    splice i s t j = t j := Function.update_of_ne h s t

/-- Interim expected utility for true type `s` reporting `r`, others truthful.
The allocation and transfer use the reported profile `splice i r t`, while
the interdependent value uses the true profile `splice i s t`.
Summation over full profiles integrates out the unused original `t i`.
-/
def interimUtil (x : Allocation) (p : Transfers)
    (i : Agent) (s r : T i) : ℝ :=
  ∑ t : Profile, weight π t *
    (value i (x (splice i r t)) (splice i s t) + p i (splice i r t))

/-- The allocation maximizes welfare at every true profile. -/
def IsEfficient (x : Allocation) : Prop :=
  ∀ t y, welfare t y ≤ welfare t (x t)

/-- Truthful reporting maximizes interim utility for every type and report. -/
def IsBIC (x : Allocation) (p : Transfers) : Prop :=
  ∀ i (s r : T i), interimUtil π x p i s r ≤ interimUtil π x p i s s

/-- Transfers sum to zero at every report profile. -/
def IsBudgetBalanced (p : Transfers) : Prop :=
  ∀ t, ∑ i, p i t = 0

/-- Each prior has total real probability mass one. -/
theorem pmf_sum_one (i : Agent) :
    (∑ s : T i, (((π i s).toNNReal : ℝ≥0) : ℝ)) = 1 := by
  have hsum : (∑ s : T i, π i s) = 1 :=
    (tsum_eq_sum (s := Finset.univ)
      (fun s hs => absurd (Finset.mem_univ s) hs)).symm.trans (π i).tsum_coe
  change (∑ s : T i, (π i s).toReal) = 1
  rw [← ENNReal.toReal_sum (fun s _ => (π i).apply_ne_top s), hsum,
    ENNReal.toReal_one]

/-- Independent joint weights sum to one. -/
theorem weight_sum_one : (∑ t : Profile, weight π t) = 1 := by
  classical
  calc
    (∑ t : Profile, weight π t) =
        ∏ i : Agent, ∑ s : T i, (((π i s).toNNReal : ℝ≥0) : ℝ) := by
      exact (Fintype.prod_sum
        (fun i s => (((π i s).toNNReal : ℝ≥0) : ℝ))).symm
    _ = 1 := by simp only [pmf_sum_one, Finset.prod_const_one]

/-- Joint weights are nonnegative. -/
theorem weight_nonneg (t : Profile) : 0 ≤ weight π t := by
  unfold weight
  exact Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)

/-- The chosen maximizer is efficient. -/
theorem xmax_efficient : IsEfficient xmax := by
  intro t y
  exact xmax_optimal t y

/-- Independent uniform priors on the four types of each agent. -/
def uniformPrior : (i : Agent) → PMF (T i) :=
  fun i => PMF.uniformOfFintype (T i)

/-- Each of the four types has real probability `1/4`. -/
theorem uniformPrior_mass (i : Agent) (s : T i) :
    (((uniformPrior i s).toNNReal : ℝ≥0) : ℝ) = 1 / 4 := by
  change (uniformPrior i s).toReal = 1 / 4
  norm_num [uniformPrior, PMF.uniformOfFintype_apply, Fintype.card_prod,
    Fintype.card_bool, ENNReal.toReal_inv]

/-- Each of the sixteen complete profiles has probability `1/16`. -/
theorem uniform_weight (t : Profile) : weight uniformPrior t = 1 / 16 := by
  norm_num [weight, uniformPrior_mass, Fin.prod_univ_two]

/-- The reversed square cycle, indexed cyclically by `Fin 4`. -/
def cycleType (j : Fin 4) : Bool × Bool :=
  if j = 0 then (false, false)
  else if j = 1 then (false, true)
  else if j = 2 then (true, true)
  else (true, false)

/-- Value-only truthful-minus-deviation sum around the reversed square.
The next report is indexed modulo four. In the corresponding BIC sum,
expected transfers telescope because the priors are independent.
-/
def cycleSum (x : Allocation) (i : Agent) : ℝ :=
  ∑ j : Fin 4,
    (interimUtil π x (fun _ _ => 0) i (cycleType j) (cycleType j) -
      interimUtil π x (fun _ _ => 0) i (cycleType j) (cycleType (j + 1)))

/-- For this concrete finite instance and independent uniform priors, no
efficient, Bayesian incentive compatible, budget-balanced mechanism exists.
M2 will supply the proof; definitions and supporting lemmas have no holes.
-/
theorem jehiel_moldovanu_impossibility :
    ∀ (x : Allocation) (p : Transfers),
      IsEfficient x → IsBIC uniformPrior x p → IsBudgetBalanced p → False := by
  sorry

end

end JM
