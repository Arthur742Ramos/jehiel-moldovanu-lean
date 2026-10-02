module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A finite welfare/incentive obstruction for independent opponent beliefs.
Balanced nonnegative deviation flows cancel arbitrary expected transfers. -/
namespace JM.Quantitative
open scoped BigOperators
noncomputable section

variable {T O K : Type*} [Fintype T] [Fintype O] [Fintype K]

/-- Lottery probabilities by own report, opposing type, and outcome. -/
abbrev Lottery (T O K : Type*) := T → O → K → ℝ

/-- Interim utility; positive transfers are received. -/
def utility (ν : O → ℝ) (v : T → O → K → ℝ)
    (q : Lottery T O K) (p : T → O → ℝ) (s r : T) : ℝ :=
  ∑ o, ν o * ((∑ k, q r o k * v s o k) + p r o)

/-- Truthful reporting loses at most `ε` against every alternative report. -/
def ApproxBIC (ν : O → ℝ) (v : T → O → K → ℝ)
    (q : Lottery T O K) (p : T → O → ℝ) (ε : ℝ) : Prop :=
  ∀ s r, utility ν v q p s r ≤ utility ν v q p s s + ε

/-- Equal incoming and outgoing deviation mass at each type. -/
def Balanced (ell : T → T → ℝ) : Prop :=
  ∀ r, (∑ s, ell r s) = ∑ s, ell s r

/-- Total mass of the flow. -/
def flowMass (ell : T → T → ℝ) : ℝ := ∑ s, ∑ r, ell s r

/-- Coefficient of a lottery entry in the value-only flow sum. -/
def coefficient (v : T → O → K → ℝ) (ell : T → T → ℝ)
    (r : T) (o : O) (k : K) : ℝ :=
  ∑ s, (ell r s * v r o k - ell s r * v s o k)

/-- Ex-ante welfare loss against the specified pointwise benchmark. -/
def welfareLoss (α : T → ℝ) (ν : O → ℝ) (W : T → O → K → ℝ)
    (g : T → O → ℝ) (q : Lottery T O K) : ℝ :=
  ∑ r, ∑ o, α r * ν o * (g r o - ∑ k, q r o k * W r o k)

/-- Balanced deviations eliminate all transfer terms. -/
theorem transfer_cancel (ell : T → T → ℝ) (hell : Balanced ell)
    (P : T → ℝ) :
    (∑ s, ∑ r, ell s r * (P s - P r)) = 0 := by
  change ∀ r, (∑ s, ell r s) = ∑ s, ell s r at hell
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun s r => ell s r * P r)]
  simp_rw [← Finset.sum_mul]
  simp_rw [← hell]
  simp only [mul_comm, sub_self]

/-- The interim flow sum is exactly its pointwise lottery functional. -/
theorem flow_identity (ν : O → ℝ) (v : T → O → K → ℝ)
    (q : Lottery T O K) (p : T → O → ℝ)
    (ell : T → T → ℝ) (hell : Balanced ell) :
    (∑ s, ∑ r, ell s r * (utility ν v q p s s - utility ν v q p s r)) =
      ∑ r, ∑ o, ∑ k, ν o * q r o k * coefficient v ell r o k := by
  let V : T → T → ℝ := fun s r => ∑ o, ∑ k, ν o * q r o k * v s o k
  let P : T → ℝ := fun r => ∑ o, ν o * p r o
  have hu (s r : T) : utility ν v q p s r = V s r + P r := by
    simp [utility, V, P, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp_rw [hu]
  simp only [add_sub_add_comm, mul_add, Finset.sum_add_distrib]
  rw [transfer_cancel ell hell P, add_zero]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun s r => ell s r * V s r)]
  simp only [coefficient, Finset.mul_sum, Finset.sum_sub_distrib, V, mul_sub]
  have hswap (f : T → T → O → K → ℝ) :
      (∑ r, ∑ s, ∑ o, ∑ k, f r s o k) = ∑ r, ∑ o, ∑ k, ∑ s, f r s o k := by
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro o _
    rw [Finset.sum_comm]
  rw [hswap, hswap]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;>
    apply Finset.sum_congr rfl <;> intro o _ <;>
    apply Finset.sum_congr rfl <;> intro k _ <;>
    apply Finset.sum_congr rfl <;> intro s _ <;> ring

/-- General quantitative certificate theorem. Taking `g` to be maximum
welfare gives an efficiency-loss bound, with unrestricted transfers. -/
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
  have hlo : -(flowMass ell * ε) ≤
      ∑ s, ∑ r, ell s r * (utility ν v q p s s - utility ν v q p s r) := by
    have hh (s r : T) : -(ell s r * ε) ≤
        ell s r * (utility ν v q p s s - utility ν v q p s r) := by
      have hc := mul_le_mul_of_nonneg_left (hBIC s r) (hell0 s r)
      nlinarith
    calc
      -(flowMass ell * ε) = ∑ s, ∑ r, -(ell s r * ε) := by
        simp [flowMass, Finset.sum_mul, Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun r _ => hh s r
  rw [flow_identity ν v q p ell hell] at hlo
  have hhi : (∑ r, ∑ o, ∑ k, ν o * q r o k * coefficient v ell r o k) ≤
      β * welfareLoss α ν W g q - a := by
    calc
      _ ≤ ∑ r, ∑ o, ∑ k, ν o * q r o k *
          (α r * (β * (g r o - W r o k) - a)) := by
        apply Finset.sum_le_sum; intro r _
        apply Finset.sum_le_sum; intro o _
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hcert r o k) (mul_nonneg (hν0 o) (hq0 r o k))
      _ = β * welfareLoss α ν W g q - a := by
        have hr (r : T) (o : O) :
            (∑ k, ν o * q r o k * (α r * (β * (g r o - W r o k) - a))) =
              β * (α r * ν o * (g r o - ∑ k, q r o k * W r o k)) -
                a * α r * ν o := by
          calc
            _ = (ν o * α r * (β * g r o - a)) * (∑ k, q r o k) -
                β * α r * ν o * (∑ k, q r o k * W r o k) := by
              simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro k _; ring
            _ = _ := by rw [hq1]; ring
        simp_rw [hr]
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [hν, mul_one, hα]
        simp [welfareLoss, Finset.mul_sum]
  linarith

end
end JM.Quantitative
