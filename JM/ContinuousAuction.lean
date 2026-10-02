module

public import JM.Binary
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
namespace JM.ContinuousAuction
open MeasureTheory Set
noncomputable section

def domain : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1
abbrev Signal := domain
attribute [local instance] Measure.Subtype.measureSpace

/-- Natural Lebesgue volume restricted to the open unit square; its total
mass is proved to be one, so no unspecified prior is hidden in this model. -/
def prior : Measure Signal := volume

/-- The two actual agents have independent copies of the uniform-square law. -/
def jointPrior : Measure (Signal × Signal) := prior.prod prior

def privateCoefficient (a : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ := a • LinearMap.fst ℝ ℝ ℝ
def socialCoefficient (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  a • LinearMap.fst ℝ ℝ ℝ - b • LinearMap.snd ℝ ℝ ℝ

def privateOpponent (b : ℝ) (o : Signal) : ℝ := b * o.val.2
def socialOpponent (a b : ℝ) (o : Signal) : ℝ := b * o.val.2 - a * o.val.1
def baseline : Signal → Signal → ℝ := fun _ _ => 0

/-- Bool true labels agent 0 and the alternative giving agent 0 the object.
Bool false labels agent 1 and the alternative giving agent 1 the object. -/
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

/-- Only agent 0's interim incentives are needed for the impossibility. The
opponent is independently drawn from the same genuine uniform-square law. -/
def Agent0BIC (a b : ℝ) (q p : Signal → Signal → ℝ) : Prop :=
  ∀ t r, utility a b q p t r ≤ utility a b q p t t

theorem domain_measurable : MeasurableSet domain := measurableSet_Ioo.prod measurableSet_Ioo

theorem uniform_probability : IsProbabilityMeasure (volume : Measure Signal) := by
  constructor
  rw [Measure.Subtype.volume_univ domain_measurable.nullMeasurableSet,
    Measure.volume_eq_prod]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)) (Ioo 0 1 ×ˢ Ioo 0 1) = 1
  rw [Measure.prod_prod, Real.volume_Ioo]
  norm_num

attribute [local instance] uniform_probability

theorem prior_probability : IsProbabilityMeasure prior := by
  unfold prior
  exact uniform_probability

attribute [local instance] prior_probability

theorem joint_probability : IsProbabilityMeasure jointPrior := by
  unfold jointPrior
  infer_instance

theorem socialOpponent_measurable (a b : ℝ) : Measurable (socialOpponent a b) := by
  unfold socialOpponent
  fun_prop

theorem socialOpponent_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (o : Signal) :
    ‖socialOpponent a b o‖ ≤ a + b := by
  rcases o.property with ⟨⟨hs0, hs1⟩, ⟨hh0, hh1⟩⟩
  have hspos : 0 ≤ a * o.val.1 := mul_nonneg ha hs0.le
  have hhpos : 0 ≤ b * o.val.2 := mul_nonneg hb hh0.le
  have hsbound : a * o.val.1 ≤ a := by
    have h := mul_nonneg ha (sub_nonneg.mpr hs1.le)
    nlinarith
  have hhbound : b * o.val.2 ≤ b := by
    have h := mul_nonneg hb (sub_nonneg.mpr hh1.le)
    nlinarith
  rw [Real.norm_eq_abs]
  unfold socialOpponent
  apply abs_le.mpr
  constructor <;> linarith

theorem socialOpponent_integrable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (socialOpponent a b) (volume : Measure Signal) := by
  exact (integrable_const (a+b)).mono' (socialOpponent_measurable a b).aestronglyMeasurable
    (ae_of_all _ (socialOpponent_bound a b ha hb))

def box (ρ : ℝ) : Set (ℝ × ℝ) :=
  Ioo ((1:ℝ)/2-ρ) (1/2+ρ) ×ˢ Ioo ((1:ℝ)/2-ρ) (1/2+ρ)

theorem box_measurable (ρ : ℝ) : MeasurableSet (box ρ) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem box_subset (ρ : ℝ) (hρ : ρ ≤ 1/4) : box ρ ⊆ domain := by
  intro x hx
  rcases hx with ⟨⟨hs0,hs1⟩,⟨hh0,hh1⟩⟩
  constructor <;> constructor <;> linarith

theorem box_mass (ρ : ℝ) (hρ : ρ ≤ 1/4) :
    (volume : Measure Signal) (Subtype.val ⁻¹' box ρ) = ENNReal.ofReal (2*ρ)^2 := by
  rw [volume_preimage_coe domain_measurable.nullMeasurableSet (box_measurable ρ),
    inter_eq_left.mpr (box_subset ρ hρ)]
  unfold box
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
  have he : (1:ℝ)/2+ρ-(1/2-ρ)=2*ρ := by ring
  rw [he, pow_two]

theorem box_positive (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1/4) :
    0 < (volume : Measure Signal) (Subtype.val ⁻¹' box ρ) := by
  rw [box_mass ρ hρ1]
  exact pos_iff_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))))

theorem midpoint_active (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (η : ℝ) (hη : 0 < η) :
    (volume : Measure Signal) {o | |(a-b)/2+socialOpponent a b o| < η} ≠ 0 := by
  let ρ := min ((1:ℝ)/4) (η/(2*(a+b)))
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1/4 := min_le_left _ _
  have hρ2 : ρ ≤ η/(2*(a+b)) := min_le_right _ _
  have hm : ρ*(2*(a+b)) ≤ η := (le_div_iff₀ (by positivity)).mp hρ2
  have hhalf : (a+b)*ρ ≤ η/2 := by linarith
  have hsub : Subtype.val ⁻¹' box ρ ⊆ {o : Signal | |(a-b)/2+socialOpponent a b o|<η} := by
    intro o ho
    rcases ho with ⟨⟨hs0,hs1⟩,⟨hh0,hh1⟩⟩
    have hs : |o.val.1-(1:ℝ)/2|<ρ := abs_lt.mpr ⟨by linarith,by linarith⟩
    have hh : |o.val.2-(1:ℝ)/2|<ρ := abs_lt.mpr ⟨by linarith,by linarith⟩
    have hbs := mul_lt_mul_of_pos_left hs ha
    have hbh := mul_lt_mul_of_pos_left hh hb
    have htri : |b*(o.val.2-(1:ℝ)/2)-a*(o.val.1-1/2)| ≤
        b*|o.val.2-1/2|+a*|o.val.1-1/2| := by
      calc
        _ ≤ |b*(o.val.2-1/2)|+|a*(o.val.1-1/2)| := by simpa using (abs_sub_le (b*(o.val.2-1/2)) 0 (a*(o.val.1-1/2)))
        _ = _ := by rw [abs_mul,abs_mul,abs_of_pos hb,abs_of_pos ha]
    have he : (a-b)/2+socialOpponent a b o = b*(o.val.2-1/2)-a*(o.val.1-1/2) := by
      unfold socialOpponent; ring
    change |(a-b)/2+socialOpponent a b o|<η
    rw [he]
    linarith
  exact ne_of_gt (lt_of_lt_of_le (box_positive ρ hρ0 hρ1) (measure_mono hsub))


theorem welfare_difference (a b : ℝ) (t o : Signal) :
    welfare a b true t o - welfare a b false t o =
      socialCoefficient a b t.val + socialOpponent a b o := by
  simp [welfare, value, socialCoefficient, socialOpponent]
  ring

theorem utility_eq_binary (a b : ℝ) (q p : Signal → Signal → ℝ) (t r : Signal) :
    utility a b q p t r =
      Binary.utility prior (privateCoefficient a) baseline (privateOpponent b) q p t r := by
  simp [utility, value, Binary.utility, privateCoefficient, baseline, privateOpponent]

theorem domain_ball : Metric.ball ((1:ℝ)/2, (1:ℝ)/2) (1/4) ⊆ domain := by
  intro x hx
  have hnorm : ‖x - ((1:ℝ)/2, (1:ℝ)/2)‖ < 1/4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hs : |x.1-(1:ℝ)/2| < 1/4 :=
    lt_of_le_of_lt (by simpa using norm_fst_le (x - ((1:ℝ)/2, (1:ℝ)/2))) hnorm
  have hh : |x.2-(1:ℝ)/2| < 1/4 :=
    lt_of_le_of_lt (by simpa using norm_snd_le (x - ((1:ℝ)/2, (1:ℝ)/2))) hnorm
  have hs' := abs_lt.mp hs
  have hh' := abs_lt.mp hh
  constructor <;> constructor <;> linarith

theorem coefficient_mismatch (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ¬ ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, privateCoefficient a v = lam * socialCoefficient a b v := by
  rintro ⟨lam, _, hc⟩
  have hs := hc (1, 0)
  have hh := hc (0, 1)
  simp [privateCoefficient, socialCoefficient] at hs hh
  rcases hh with hz | hz
  · rw [hz] at hs
    linarith
  · linarith

theorem privateOpponent_integrable (b : ℝ) (hb : 0 ≤ b) :
    Integrable (privateOpponent b) prior := by
  have hm : Measurable (privateOpponent b) := by unfold privateOpponent; fun_prop
  apply (integrable_const b).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro o
  have h0 := o.property.2.1
  have h1 := o.property.2.2
  rw [Real.norm_eq_abs, privateOpponent, abs_mul, abs_of_nonneg hb, abs_of_pos h0]
  nlinarith

theorem active_threshold (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Binary.Active prior (socialCoefficient a b) (socialOpponent a b)
      ((1:ℝ)/2, (1:ℝ)/2) := by
  intro η hη
  have hc : socialCoefficient a b ((1:ℝ)/2, (1:ℝ)/2) = (a-b)/2 := by
    simp [socialCoefficient]; ring
  change (volume : Measure Signal) {o | |socialCoefficient a b (1/2, 1/2) +
    socialOpponent a b o| < η} ≠ 0
  rw [hc]
  exact midpoint_active a b ha hb η hη

/-- Every expected utility in the actual auction model is well defined. -/
theorem utility_integrable (a b : ℝ) (hb : 0 ≤ b) {q p : Signal → Signal → ℝ}
    (hq : Binary.Lottery q) (hp : Binary.Transfers prior p) (t r : Signal) :
    Integrable (fun o => q r o * value a b true true t o +
      (1 - q r o) * value a b true false t o + p r o) prior := by
  have hg : ∀ t : Signal, Integrable (baseline t) prior := fun _ => integrable_const 0
  have hd := privateOpponent_integrable b hb
  have hi := Binary.utility_integrable prior (privateCoefficient a) baseline
    (privateOpponent b) hg hd hq hp t r
  simpa [value, baseline, privateCoefficient, privateOpponent] using hi

/-- On a genuine continuous independent uniform-square type model, positive
own and external coefficients prohibit efficiency even with only agent 0 BIC.
The theorem allows arbitrary measurable lotteries and integrable transfers. -/
theorem impossibility (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (q p : Signal → Signal → ℝ) (hq : Binary.Lottery q)
    (hp : Binary.Transfers prior p) (he : Efficient a b q) (hB : Agent0BIC a b q p) :
    False := by
  have hg : ∀ t : Signal, Integrable (baseline t) prior := fun _ => integrable_const 0
  have hd := privateOpponent_integrable b hb.le
  have hE : Binary.Efficient (socialCoefficient a b) (socialOpponent a b) q := by
    intro t o
    have hx := he t o
    rw [welfare_difference] at hx
    exact hx
  have hB' : Binary.BIC prior (privateCoefficient a) baseline (privateOpponent b) q p := by
    intro t r
    simpa only [← utility_eq_binary] using hB t r
  have hA : socialCoefficient a b ≠ 0 := by
    intro hz
    have hx := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f (1, 0)) hz
    simp [socialCoefficient] at hx
    linarith
  have hc := Binary.congruence prior (privateCoefficient a) (socialCoefficient a b)
    baseline (privateOpponent b) (socialOpponent a b) hg hd hq hp hB' hE (socialOpponent_measurable a b) hA
    (1/2, 1/2) (1/4) (by norm_num) domain_ball (active_threshold a b ha hb)
  exact coefficient_mismatch a b ha hb hc

end
end JM.ContinuousAuction
