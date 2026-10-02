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

/-- The two agents are distinct. -/
lemma n10 : (1 : Fin 2) ≠ 0 := by decide

lemma n01 : (0 : Fin 2) ≠ 1 := by decide

lemma other0 : other 0 = 1 := rfl

lemma other1 : other 1 = 0 := rfl

lemma c0 : cycleType 0 = (false, false) := rfl

lemma c1 : cycleType 1 = (false, true) := rfl

lemma c2 : cycleType 2 = (true, true) := rfl

lemma c3 : cycleType 3 = (true, false) := rfl

lemma e01 : (0 : Fin 4) + 1 = 1 := rfl

lemma e12 : (1 : Fin 4) + 1 = 2 := rfl

lemma e23 : (2 : Fin 4) + 1 = 3 := rfl

lemma e30 : (3 : Fin 4) + 1 = 0 := rfl

/-- Separate the value and transfer contributions to interim utility. -/
lemma interimUtil_split (x : Allocation) (p : Transfers) (i : Agent) (s r : T i) :
    interimUtil π x p i s r =
      (∑ t : Profile, weight π t * value i (x (splice i r t)) (splice i s t)) +
      (∑ t : Profile, weight π t * p i (splice i r t)) := by
  simp only [interimUtil, mul_add, Finset.sum_add_distrib]

/-- Expected transfers telescope around the closed four-type cycle. -/
lemma transfer_cycle_zero (p : Transfers) (i : Agent) :
    ∑ j : Fin 4,
      ((∑ t : Profile, weight π t * p i (splice i (cycleType j) t)) -
        (∑ t : Profile, weight π t * p i (splice i (cycleType (j + 1)) t))) = 0 := by
  rw [Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  simp only [Fin.sum_univ_four, e01, e12, e23, e30]
  ac_rfl

/-- Adding arbitrary transfers leaves the closed-cycle utility sum unchanged. -/
lemma transfer_telescope (x : Allocation) (p : Transfers) (i : Agent) :
    ∑ j : Fin 4,
      (interimUtil π x p i (cycleType j) (cycleType j) -
        interimUtil π x p i (cycleType j) (cycleType (j + 1))) =
      cycleSum (π := π) x i := by
  simp only [cycleSum, interimUtil_split, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [add_sub_add_comm, Finset.sum_add_distrib, transfer_cycle_zero, add_zero]

/-- Every cycle inequality follows by summing the four BIC inequalities. -/
lemma cycleSum_nonneg (x : Allocation) (p : Transfers) (hBIC : IsBIC π x p)
    (i : Agent) : 0 ≤ cycleSum (π := π) x i := by
  rw [← transfer_telescope (π := π) x p i]
  apply Finset.sum_nonneg
  intro j _
  exact sub_nonneg.mpr (hBIC i (cycleType j) (cycleType (j + 1)))

/-- Summing a function of agent one's type integrates out agent zero's type. -/
lemma sum_profile_factor_one (F : T 1 → ℝ) :
    ∑ t : Profile, F (t 1) = 4 * ∑ t1 : T 1, F t1 := by
  have h : ∑ t : Profile, F (t 1) = ∑ p : T 0 × T 1, F p.2 := by
    refine Fintype.sum_equiv (piFinTwoEquiv T) _ _ (fun t => ?_)
    rfl
  rw [h, Fintype.sum_prod_type]
  change (∑ _ : T 0, ∑ t1 : T 1, F t1) = 4 * ∑ t1 : T 1, F t1
  rw [Finset.sum_const, Finset.card_univ]
  simp [T, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]

/-- Summing a function of agent zero's type integrates out agent one's type. -/
lemma sum_profile_factor_zero (F : T 0 → ℝ) :
    ∑ t : Profile, F (t 0) = 4 * ∑ t0 : T 0, F t0 := by
  have h : ∑ t : Profile, F (t 0) = ∑ p : T 0 × T 1, F p.1 := by
    refine Fintype.sum_equiv (piFinTwoEquiv T) _ _ (fun t => ?_)
    rfl
  rw [h, Fintype.sum_prod_type]
  simp [T, Finset.sum_const, Fintype.card_prod, Fintype.card_bool,
    nsmul_eq_mul, ← Finset.mul_sum]

/-- Splicing agent zero produces the corresponding two-entry profile. -/
lemma key0 (r : T 0) (t : Profile) :
    Function.update t 0 r = (![r, t 1] : Profile) := by
  funext j
  fin_cases j
  · exact Function.update_self 0 r t
  · exact Function.update_of_ne n10 r t

/-- Splicing agent one produces the corresponding two-entry profile. -/
lemma key1 (r : T 1) (t : Profile) :
    Function.update t 1 r = (![t 0, r] : Profile) := by
  funext j
  fin_cases j
  · exact Function.update_of_ne n01 r t
  · exact Function.update_self 1 r t

/-- Uniform interim utility for agent zero is an average over four opposing types. -/
lemma interimUtil_zero (x : Allocation) (p : Transfers) (s r : T 0) :
    interimUtil uniformPrior x p 0 s r =
      ∑ t1 : T 1, (1 / 4 : ℝ) *
        (value 0 (x ![r, t1]) ![s, t1] + p 0 ![r, t1]) := by
  simp only [interimUtil, splice, uniform_weight]
  simp_rw [key0]
  rw [sum_profile_factor_one
    (fun t1 => (1 / 16 : ℝ) * (value 0 (x ![r, t1]) ![s, t1] + p 0 ![r, t1])),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t1 _
  rw [← mul_assoc]
  norm_num

/-- Uniform interim utility for agent one is an average over four opposing types. -/
lemma interimUtil_one (x : Allocation) (p : Transfers) (s r : T 1) :
    interimUtil uniformPrior x p 1 s r =
      ∑ t0 : T 0, (1 / 4 : ℝ) *
        (value 1 (x ![t0, r]) ![t0, s] + p 1 ![t0, r]) := by
  simp only [interimUtil, splice, uniform_weight]
  simp_rw [key1]
  rw [sum_profile_factor_zero
    (fun t0 => (1 / 16 : ℝ) * (value 1 (x ![t0, r]) ![t0, s] + p 1 ![t0, r])),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t0 _
  rw [← mul_assoc]
  norm_num

/-- Every alternative in the two-element set is zero or one. -/
lemma alternative_cases (k : X) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

/-- A strict welfare advantage forces an efficient allocation to choose zero. -/
lemma efficient_winner_zero (x : Allocation) (hx : IsEfficient x) (t : Profile)
    (hlt : welfare t 1 < welfare t 0) : x t = 0 := by
  rcases alternative_cases (x t) with h | h
  · exact h
  · have hle := hx t 0
    rw [h] at hle
    exact False.elim ((not_lt_of_ge hle) hlt)

/-- A strict welfare advantage forces an efficient allocation to choose one. -/
lemma efficient_winner_one (x : Allocation) (hx : IsEfficient x) (t : Profile)
    (hlt : welfare t 0 < welfare t 1) : x t = 1 := by
  rcases alternative_cases (x t) with h | h
  · have hle := hx t 1
    rw [h] at hle
    exact False.elim ((not_lt_of_ge hle) hlt)
  · exact h

/-- Efficiency fixes twelve profiles; all sixteen choices at the four ties
have the same combined value-only cycle sum. -/
lemma cycleSum_pair (x : Allocation) (hx : IsEfficient x) :
    cycleSum (π := uniformPrior) x 0 + cycleSum (π := uniformPrior) x 1 = -1 / 2 := by
  have e_FF_FT : x (![(false, false), (false, true)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_FF_TF : x (![(false, false), (true, false)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_FF_TT : x (![(false, false), (true, true)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_FT_FF : x (![(false, true), (false, false)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_FT_TF : x (![(false, true), (true, false)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_FT_TT : x (![(false, true), (true, true)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TF_FF : x (![(true, false), (false, false)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TF_FT : x (![(true, false), (false, true)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TF_TT : x (![(true, false), (true, true)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TT_FF : x (![(true, true), (false, false)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TT_FT : x (![(true, true), (false, true)] : Profile) = 0 := by
    apply efficient_winner_zero x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have e_TT_TF : x (![(true, true), (true, false)] : Profile) = 1 := by
    apply efficient_winner_one x hx
    norm_num [welfare, Fin.sum_univ_two, value, valA, valB, c, other,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases alternative_cases (x (![(false, false), (false, false)] : Profile)) with h00 | h00 <;>
  rcases alternative_cases (x (![(false, true), (false, true)] : Profile)) with h11 | h11 <;>
  rcases alternative_cases (x (![(true, true), (true, true)] : Profile)) with h22 | h22 <;>
  rcases alternative_cases (x (![(true, false), (true, false)] : Profile)) with h33 | h33 <;>
    simp only [cycleSum, Fin.sum_univ_four, e01, e12, e23, e30,
      c0, c1, c2, c3, interimUtil_zero, interimUtil_one] <;>
    simp only [T, Fintype.sum_prod_type, Fintype.sum_bool] <;>
    simp only [e_FF_FT, e_FF_TF, e_FF_TT, e_FT_FF, e_FT_TF, e_FT_TT,
      e_TF_FF, e_TF_FT, e_TF_TT, e_TT_FF, e_TT_FT, e_TT_TF, h00, h11, h22, h33] <;>
    norm_num [value, valA, valB, c, other, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- For this concrete finite instance and independent uniform priors, no
efficient, Bayesian incentive compatible, budget-balanced mechanism exists.
M2 will supply the proof; definitions and supporting lemmas have no holes.
-/
theorem jehiel_moldovanu_impossibility :
    ∀ (x : Allocation) (p : Transfers),
      IsEfficient x → IsBIC uniformPrior x p → IsBudgetBalanced p → False := by
  intro x p hxEff hxBIC _
  have h0 := cycleSum_nonneg (π := uniformPrior) x p hxBIC 0
  have h1 := cycleSum_nonneg (π := uniformPrior) x p hxBIC 1
  have hsum := cycleSum_pair x hxEff
  linarith

end

end JM
