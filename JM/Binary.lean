module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section
namespace JM.Binary
open MeasureTheory
noncomputable section

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω]

/-- A binary probability is efficient at welfare difference W. Ties permit
every probability in [0,1]. Alternative 1 minus alternative 0 is the sign convention. -/
def EfficientAt (q W : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ (0 < W → q = 1) ∧ (W < 0 → q = 0)

/-- Own reports are actual members of U; opposing states have one fixed law.
Private alternative-0 values are g; private differences are c(t)+d(o).
Total social differences are A(t)+H(o). No participation or budget condition. -/
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lottery_norm {U : Set E} {q : U → Ω → ℝ} (hq : Lottery q) (r : U) (o : Ω) :
    ‖q r o‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hq.2 r o).1]
  exact (hq.2 r o).2

theorem lottery_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} {q : U → Ω → ℝ} (hq : Lottery q) (r : U) : Integrable (q r) μ := by
  exact (integrable_const (1 : ℝ)).mono' (hq.1 r).aestronglyMeasurable
    (ae_of_all _ (lottery_norm hq r))

theorem lottery_mul_integrable (μ : Measure Ω) {U : Set E} {q : U → Ω → ℝ}
    (hq : Lottery q) (r : U) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun o => q r o * f o) μ :=
  hf.bdd_mul (hq.1 r).aestronglyMeasurable (ae_of_all _ (lottery_norm hq r))

/-- Every utility integral used by BIC is integrable, so Bochner totalization
cannot create an incentive inequality from undefined expected utilities. -/
theorem utility_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (t r : U) :
    Integrable (fun o => g t o + q r o * (c t.val + d o) + p r o) μ := by
  exact ((hg t).add (lottery_mul_integrable μ hq r ((integrable_const _).add hd))).add
    (hp r)

theorem utility_decomposition (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (t r : U) :
    utility μ c g d q p t r = (∫ o, g t o ∂μ) +
      c t.val * probability μ q r + (∫ o, q r o * d o + p r o ∂μ) := by
  have hi := lottery_integrable μ hq r
  have hj := lottery_mul_integrable μ hq r hd
  have he : (fun o => g t o + q r o * (c t.val + d o) + p r o) =
      (fun o => (g t o + c t.val * q r o) + (q r o * d o + p r o)) := by
    funext o; ring
  unfold utility probability
  rw [he]
  calc
    _ = (∫ o, g t o + c t.val * q r o ∂μ) +
        (∫ o, q r o * d o + p r o ∂μ) :=
      integral_add ((hg t).add (hi.const_mul (c t.val))) (hj.add (hp r))
    _ = _ := by rw [integral_add (hg t) (hi.const_mul (c t.val)), integral_const_mul]

theorem weak_monotonicity (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (hb : BIC μ c g d q p) (t s : U) :
    0 ≤ (c t.val - c s.val) * (probability μ q t - probability μ q s) := by
  have ht := hb t s
  have hs := hb s t
  rw [utility_decomposition μ c g d hg hd hq hp,
    utility_decomposition μ c g d hg hd hq hp] at ht hs
  nlinarith

theorem efficient_monotone (q r V W : ℝ) (hq : EfficientAt q W)
    (hr : EfficientAt r V) (h : V < W) : r ≤ q := by
  obtain ⟨hq0, hq1, hqp, hqn⟩ := hq
  obtain ⟨hr0, hr1, hrp, hrn⟩ := hr
  by_cases hp : 0 < W
  · rw [hqp hp]; exact hr1
  · rw [hrn (by linarith)]; exact hq0

theorem proportional_of_product_nonneg (c A : E →ₗ[ℝ] ℝ) (w : E) (hw : A w = 1)
    (h : ∀ v, 0 ≤ c v * A v) : ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  have hker : ∀ v, A v = 0 → c v = 0 := by
    intro v hv
    by_contra hc
    have hn := h (w - ((c w + 1) / c v) • v)
    simp only [map_sub, map_smul, smul_eq_mul, hw, hv, mul_zero, sub_zero] at hn
    have he : (c w + 1) / c v * c v = c w + 1 := by field_simp
    rw [he] at hn
    nlinarith
  refine ⟨c w, ?_, ?_⟩
  · simpa [hw] using h w
  · intro v
    have he := hker (v - A v • w) (by simp [hw])
    simp only [map_sub, map_smul, smul_eq_mul] at he
    nlinarith

theorem strict_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} {A : E →ₗ[ℝ] ℝ} {H : Ω → ℝ} {q : U → Ω → ℝ}
    (hq : Lottery q) (he : Efficient A H q) {t0 : E} (ha : Active μ A H t0)
    (tp tm : U) (eps : ℝ) (hep : 0 < eps)
    (hp : A tp.val = A t0 + eps) (hm : A tm.val = A t0 - eps) :
    probability μ q tm < probability μ q tp := by
  have hn : ∀ o, 0 ≤ q tp o - q tm o := by
    intro o
    exact sub_nonneg.mpr (efficient_monotone _ _ _ _ (he tp o) (he tm o)
      (by rw [hp, hm]; linarith))
  have hb : {o | |A t0 + H o| < eps} ⊆
      Function.support (fun o => q tp o - q tm o) := by
    intro o ho
    change |A t0 + H o| < eps at ho
    have hz := abs_lt.mp ho
    have hpt : q tp o = 1 := (he tp o).2.2.1 (by rw [hp]; linarith)
    have hmt : q tm o = 0 := (he tm o).2.2.2 (by rw [hm]; linarith)
    simp [Function.support, hpt, hmt]
  have hpos : 0 < μ (Function.support (fun o => q tp o - q tm o)) :=
    lt_of_lt_of_le (pos_iff_ne_zero.mpr (ha eps hep)) (measure_mono hb)
  have hi := (lottery_integrable μ hq tp).sub (lottery_integrable μ hq tm)
  have hx := (integral_pos_iff_support_of_nonneg hn hi).mpr hpos
  rw [integral_sub (lottery_integrable μ hq tp) (lottery_integrable μ hq tm)] at hx
  exact sub_pos.mp hx

theorem symmetric_types {U : Set E} {t0 : E} {rad : ℝ} (hrad : 0 < rad)
    (hball : Metric.ball t0 rad ⊆ U) (h : E) :
    ∃ δ : ℝ, 0 < δ ∧ t0 + δ • h ∈ U ∧ t0 - δ • h ∈ U := by
  let δ := rad / (2 * (‖h‖ + 1))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hn : 0 ≤ ‖h‖ := norm_nonneg _
  have hden : 2 * (‖h‖ + 1) ≠ 0 := by positivity
  have heq : δ * (2 * (‖h‖ + 1)) = rad := by dsimp [δ]; field_simp
  have hb : ‖δ • h‖ < rad := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  refine ⟨δ, hd, hball ?_, hball ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm] using hb
  · simpa [Metric.mem_ball, dist_eq_norm] using hb

/-- The active support cut forces alignment on every direction of a genuine
open own-type ball; opposing distributions can be atomic or continuous. -/
theorem congruence (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (hb : BIC μ c g d q p)
    (he : Efficient A H q) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) : ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  have hdir : ∀ h : E, 0 < A h → 0 ≤ c h := by
    intro h hAh
    obtain ⟨δ, hδ, htp, htm⟩ := symmetric_types hrad hball h
    let tp : U := ⟨t0 + δ • h, htp⟩
    let tm : U := ⟨t0 - δ • h, htm⟩
    have hqp := strict_probability μ hq he ha tp tm (δ * A h) (mul_pos hδ hAh)
      (by simp [tp]) (by simp [tm])
    have hw := weak_monotonicity μ c g d hg hd hq hp hb tp tm
    have hct : c tp.val - c tm.val = 2 * δ * c h := by simp [tp, tm]; ring
    rw [hct] at hw
    have hpd : 0 < probability μ q tp - probability μ q tm := sub_pos.mpr hqp
    by_contra hn
    have hc : c h < 0 := lt_of_not_ge hn
    have hx : 2 * δ * c h * (probability μ q tp - probability μ q tm) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hc) hpd
    linarith
  have hprod : ∀ h : E, 0 ≤ c h * A h := by
    intro h
    rcases lt_trichotomy (A h) 0 with hn | hz | hp
    · have hh := hdir (-h) (by simpa using neg_pos.mpr hn)
      have hc : c h ≤ 0 := by simpa using hh
      exact mul_nonneg_of_nonpos_of_nonpos hc (le_of_lt hn)
    · simp [hz]
    · exact mul_nonneg (hdir h hp) (le_of_lt hp)
  have hex : ∃ v : E, A v ≠ 0 := by
    by_contra hh
    apply hA
    ext v
    simpa using (not_exists.mp hh v)
  obtain ⟨v, hv⟩ := hex
  exact proportional_of_product_nonneg c A ((A v)⁻¹ • v) (by simp [hv]) hprod

theorem efficient_maximizes (q r W : ℝ) (hq : EfficientAt q W)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : r * W ≤ q * W := by
  rcases lt_trichotomy W 0 with hn | hz | hp
  · rw [hq.2.2.2 hn]; nlinarith
  · simp [hz]
  · rw [hq.2.2.1 hp]; nlinarith

def alignedTransfers {U : Set E} (lam : ℝ) (d H : Ω → ℝ) (q : U → Ω → ℝ) :
    U → Ω → ℝ := fun r o => (lam * H o - d o) * q r o

/-- Opponents are held at their actual types. This is not truthfulness against
arbitrary opponent misreports in an interdependent-value game. -/
def ExPostIC {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    (q p : U → Ω → ℝ) : Prop := ∀ t r o,
  g t o + q r o * (c t.val + d o) + p r o ≤
  g t o + q t o * (c t.val + d o) + p t o

theorem aligned_transfers_integrable (μ : Measure Ω) {U : Set E}
    (lam : ℝ) (d H : Ω → ℝ) {q : U → Ω → ℝ} (hq : Lottery q)
    (hd : Integrable d μ) (hH : Integrable H μ) :
    Transfers μ (alignedTransfers lam d H q) := by
  intro r
  change Integrable (fun o => (lam * H o - d o) * q r o) μ
  have hi := lottery_mul_integrable μ hq r ((hH.const_mul lam).sub hd)
  convert hi using 1
  funext o
  exact mul_comm _ _

theorem aligned_ex_post (c A : E →ₗ[ℝ] ℝ) {U : Set E} (g : U → Ω → ℝ)
    (d H : Ω → ℝ) {q : U → Ω → ℝ} (hq : Lottery q) (he : Efficient A H q)
    (lam : ℝ) (hl : 0 ≤ lam) (hc : ∀ v, c v = lam * A v) :
    ExPostIC c g d q (alignedTransfers lam d H q) := by
  intro t r o
  have hm := efficient_maximizes (q t o) (q r o) (A t.val + H o)
    (he t o) (hq.2 r o).1 (hq.2 r o).2
  have hs := mul_le_mul_of_nonneg_left hm hl
  simp only [alignedTransfers, hc]
  nlinarith

theorem ex_post_implies_bic (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d : Ω → ℝ)
    {q p : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hq : Lottery q) (hp : Transfers μ p) (he : ExPostIC c g d q p) :
    BIC μ c g d q p := by
  intro t r
  exact integral_mono (utility_integrable μ c g d hg hd hq hp t r)
    (utility_integrable μ c g d hg hd hq hp t t) (he t r)

/-- Every measurable efficient binary lottery has an integrable BIC transfer
implementation exactly when private and social coefficients align. -/
theorem implementation_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    {q : U → Ω → ℝ} (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hH : Integrable H μ) (hq : Lottery q) (he : Efficient A H q) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) :
    (∃ p : U → Ω → ℝ, Transfers μ p ∧ BIC μ c g d q p) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  constructor
  · rintro ⟨p, hp, hb⟩
    exact congruence μ c A g d H hg hd hq hp hb he hmH hA t0 rad hrad hball ha
  · rintro ⟨lam, hl, hc⟩
    have hp := aligned_transfers_integrable μ lam d H hq hd hH
    exact ⟨alignedTransfers lam d H q, hp, ex_post_implies_bic μ c g d hg hd hq hp
      (aligned_ex_post c A g d H hq he lam hl hc)⟩

def thresholdLottery {U : Set E} (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ) :
    U → Ω → ℝ := fun r o => if 0 < A r.val + H o then 1 else 0

theorem threshold_lottery {U : Set E} (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ)
    (hH : Measurable H) : Lottery (thresholdLottery (U := U) A H) := by
  constructor
  · intro r
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_const.add hH))
      measurable_const measurable_const
  · intro r o; unfold thresholdLottery; split_ifs <;> norm_num

omit [MeasurableSpace Ω] in
theorem threshold_efficient {U : Set E} (A : E →ₗ[ℝ] ℝ) (H : Ω → ℝ) :
    Efficient A H (thresholdLottery (U := U) A H) := by
  intro r o
  unfold EfficientAt thresholdLottery
  by_cases hh : 0 < A r.val + H o
  · simp [hh]; linarith
  · simp [hh]

/-- A genuine mechanism exists iff alignment; thresholdLottery supplies an
efficient measurable witness, so this existential is not allocation-vacuous. -/
theorem efficient_bic_exists_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {U : Set E} (c A : E →ₗ[ℝ] ℝ) (g : U → Ω → ℝ) (d H : Ω → ℝ)
    (hg : ∀ t, Integrable (g t) μ) (hd : Integrable d μ)
    (hH : Integrable H μ) (hmH : Measurable H) (hA : A ≠ 0)
    (t0 : E) (rad : ℝ) (hrad : 0 < rad) (hball : Metric.ball t0 rad ⊆ U)
    (ha : Active μ A H t0) :
    (∃ q p : U → Ω → ℝ, Lottery q ∧ Transfers μ p ∧ Efficient A H q ∧
      BIC μ c g d q p) ↔ ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v, c v = lam * A v := by
  constructor
  · rintro ⟨q, p, hq, hp, he, hb⟩
    exact congruence μ c A g d H hg hd hq hp hb he hmH hA t0 rad hrad hball ha
  · intro hc
    let q := thresholdLottery (U := U) A H
    have hq : Lottery q := threshold_lottery A H hmH
    have he : Efficient A H q := threshold_efficient A H
    obtain ⟨p, hp, hb⟩ := (implementation_iff μ c A g d H hg hd hH hq he hmH hA
      t0 rad hrad hball ha).mpr hc
    exact ⟨q, p, hq, hp, he, hb⟩

end
end JM.Binary
