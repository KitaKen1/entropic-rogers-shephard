import EntropicRogersShephard.BoundedDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Real densities as measures and normalized difference-slice probability measures. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def realDensityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : Measure α := μ.withDensity (fun x => ENNReal.ofReal (f x))

theorem realDensityMeasure_univ {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hi : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    realDensityMeasure μ f univ = ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [realDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)).symm

theorem isProbabilityMeasure_realDensityMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hi : Integrable f μ) (hn : ∀ x, 0 ≤ f x)
    (hm : (∫ x, f x ∂μ) = 1) : IsProbabilityMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_univ hi hn, hm, ENNReal.ofReal_one]

theorem integral_realDensityMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) (g : α → ℝ) :
    (∫ x, g x ∂realDensityMeasure μ f) = ∫ x, f x * g x ∂μ := by
  rw [realDensityMeasure, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

theorem integrable_realDensityMeasure_iff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    Integrable g (realDensityMeasure μ f) ↔ Integrable (fun x => f x * g x) μ := by
  rw [realDensityMeasure, integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

noncomputable def differenceSliceDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) :
    (Fin n → ℝ) → ℝ := fun x => f x * f (x - s) / differenceDensity f s

theorem measurable_differenceSliceDensity {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (s : Fin n → ℝ) : Measurable (differenceSliceDensity f s) :=
  (hf.mul (hf.comp (measurable_id.sub measurable_const))).div_const _

theorem differenceSliceDensity_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (s x : Fin n → ℝ) : 0 ≤ differenceSliceDensity f s x :=
  div_nonneg (mul_nonneg (hf x) (hf (x - s))) (crossDifferenceDensity_nonneg hf hf s)

theorem integrable_differenceSliceDensity {n : ℕ} {f : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hf : IsProbabilityDensity n f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) M) (s : Fin n → ℝ) :
    Integrable (differenceSliceDensity f s) volume :=
  (integrable_difference_slice_of_bounded hf hf.1 hb s).div_const _

theorem integral_differenceSliceDensity {n : ℕ} {f : (Fin n → ℝ) → ℝ} {s : Fin n → ℝ}
    (hs : differenceDensity f s ≠ 0) : (∫ x, differenceSliceDensity f s x) = 1 := by
  change (∫ x, f x * f (x - s) / differenceDensity f s) = 1
  rw [integral_div]
  exact div_self hs

noncomputable def differenceSliceMeasure {n : ℕ} (f : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) :
    Measure (Fin n → ℝ) := realDensityMeasure volume (differenceSliceDensity f s)

theorem isProbabilityMeasure_differenceSliceMeasure {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {M : ℝ} (hf : IsProbabilityDensity n f)
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) M) {s : Fin n → ℝ} (hs : 0 < differenceDensity f s) :
    IsProbabilityMeasure (differenceSliceMeasure f s) :=
  isProbabilityMeasure_realDensityMeasure (integrable_differenceSliceDensity hf hb s)
    (differenceSliceDensity_nonneg hf.2.1 s) (integral_differenceSliceDensity hs.ne')

theorem integral_differenceSliceMeasure {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) (s : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ) :
    (∫ x, g x ∂differenceSliceMeasure f s) =
      (∫ x, f x * f (x - s) * g x) / differenceDensity f s := by
  rw [differenceSliceMeasure, integral_realDensityMeasure
    (measurable_differenceSliceDensity hf s) (differenceSliceDensity_nonneg hn s)]
  have he : (fun x => differenceSliceDensity f s x * g x) =
      (fun x => (f x * f (x - s) * g x) / differenceDensity f s) := by
    funext x
    dsimp [differenceSliceDensity]
    ring
  rw [he, integral_div]

end EntropicRogersShephard
