import EntropicRogersShephard
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
Probability-density connections for the geometric calculations.
Unit simplex volumes remain symbolic throughout this module.
-/

open MeasureTheory Set Finset
open scoped ENNReal Convolution

namespace EntropicRogersShephard

/-- Difference convolution, allowing two different input densities. -/
noncomputable def crossDifferenceDensity {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) : ℝ :=
  ∫ x, f x * g (x - s)

theorem crossDifferenceDensity_nonneg {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (s : Fin n → ℝ) :
    0 ≤ crossDifferenceDensity f g s :=
  integral_nonneg fun x => mul_nonneg (hf x) (hg (x - s))

theorem measurable_crossDifferenceDensity {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (crossDifferenceDensity f g) := by
  have h : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f p.2 * g (p.2 - p.1)) :=
    (hf.comp measurable_snd).mul (hg.comp (measurable_snd.sub measurable_fst))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem crossDifferenceDensity_eq_convolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) :
    crossDifferenceDensity f g =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x => g (-x)) := by
  funext s
  simp [crossDifferenceDensity, convolution_def, neg_sub]

theorem integrable_crossDifferenceDensity {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (crossDifferenceDensity f g) volume := by
  rw [crossDifferenceDensity_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.comp_neg

theorem integral_crossDifferenceDensity {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ s, crossDifferenceDensity f g s) = (∫ x, f x) * ∫ x, g x := by
  rw [crossDifferenceDensity_eq_convolution]
  simpa only [ContinuousLinearMap.mul_apply', integral_neg_eq_self] using
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hg.comp_neg

theorem isProbabilityDensity_crossDifferenceDensity {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f)
    (hg : IsProbabilityDensity n g) : IsProbabilityDensity n (crossDifferenceDensity f g) := by
  refine ⟨measurable_crossDifferenceDensity hf.1 hg.1,
    crossDifferenceDensity_nonneg hf.2.1 hg.2.1,
    integrable_crossDifferenceDensity hf.2.2.1 hg.2.2.1, ?_⟩
  rw [integral_crossDifferenceDensity hf.2.2.1 hg.2.2.1, hf.2.2.2, hg.2.2.2, one_mul]

theorem isProbabilityDensity_differenceDensity {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) : IsProbabilityDensity n (differenceDensity f) :=
  isProbabilityDensity_crossDifferenceDensity hf hf

/-- A normalized uniform density; the positivity and finiteness hypotheses occur below. -/
noncomputable def uniformDensity {n : ℕ} (A : Set (Fin n → ℝ)) : (Fin n → ℝ) → ℝ :=
  A.indicator (fun _ => (volume A).toReal⁻¹)

theorem measurable_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Measurable (uniformDensity A) := measurable_const.indicator hA

theorem uniformDensity_nonneg {n : ℕ} (A : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    0 ≤ uniformDensity A x := by
  apply Set.indicator_nonneg
  intro _ _
  positivity

theorem integrable_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞) :
    Integrable (uniformDensity A) volume := by
  rw [uniformDensity, integrable_indicator_iff hA]
  exact integrableOn_const hfin

theorem integral_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hpos : volume A ≠ 0) (hfin : volume A ≠ ∞) :
    (∫ x, uniformDensity A x) = 1 := by
  rw [uniformDensity, integral_indicator_const _ hA, smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩)

theorem isProbabilityDensity_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hpos : volume A ≠ 0) (hfin : volume A ≠ ∞) :
    IsProbabilityDensity n (uniformDensity A) :=
  ⟨measurable_uniformDensity hA, uniformDensity_nonneg A,
    integrable_uniformDensity hA hfin, integral_uniformDensity hA hpos hfin⟩

theorem integrable_negMulLog_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞) :
    Integrable (fun x => Real.negMulLog (uniformDensity A x)) volume := by
  apply integrable_negMulLog_of_bounded_support hA hfin (measurable_uniformDensity hA)
    (C := (volume A).toReal⁻¹)
  · intro x
    refine ⟨uniformDensity_nonneg A x, ?_⟩
    by_cases hx : x ∈ A
    · simp [uniformDensity, hx]
    · simp only [uniformDensity, Set.indicator_of_notMem hx]
      positivity
  · intro x hx
    simp [uniformDensity, hx]

theorem differentialEntropy_uniformDensity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hpos : volume A ≠ 0) (hfin : volume A ≠ ∞) :
    differentialEntropy (uniformDensity A) volume = Real.log (volume A).toReal := by
  have hv : (volume A).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩
  have he : (fun x => Real.negMulLog (uniformDensity A x)) =
      A.indicator (fun _ => Real.negMulLog (volume A).toReal⁻¹) := by
    funext x
    by_cases hx : x ∈ A <;> simp [uniformDensity, hx]
  rw [differentialEntropy, he, integral_indicator_const _ hA, smul_eq_mul]
  simp only [Real.negMulLog_def, Real.log_inv, measureReal_def]
  field_simp

theorem volume_simplex_ne_top (m : ℕ) (a : ℝ) : volume (simplex m a) ≠ ∞ :=
  (isCompact_simplex m a).measure_ne_top

theorem small_box_subset_simplex (m : ℕ) :
    Icc (0 : Fin m → ℝ) (fun _ => 1 / ((m : ℝ) + 1)) ⊆ simplex m 1 := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  calc
    ∑ i, x i ≤ ∑ _ : Fin m, 1 / ((m : ℝ) + 1) := Finset.sum_le_sum fun i _ => hx.2 i
    _ = (m : ℝ) / ((m : ℝ) + 1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)

theorem volume_unit_simplex_pos (m : ℕ) : 0 < volume (simplex m 1) := by
  have hb : 0 < volume (Icc (0 : Fin m → ℝ) (fun _ => 1 / ((m : ℝ) + 1))) := by
    rw [Real.volume_Icc_pi]
    apply bot_lt_iff_ne_bot.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply (ENNReal.ofReal_pos.mpr ?_).ne'
    simp only [Pi.zero_apply, sub_zero]
    positivity
  exact hb.trans_le (measure_mono (small_box_subset_simplex m))

theorem volume_simplex_pos_of_pos (m : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < volume (simplex m a) := by
  rw [volume_simplex_pos m ha]
  exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
    (ENNReal.ofReal_pos.mpr (pow_pos ha m)).ne' (volume_unit_simplex_pos m).ne')

theorem isProbabilityDensity_uniformSimplex (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityDensity m (uniformDensity (simplex m a)) :=
  isProbabilityDensity_uniformDensity (isClosed_simplex m a).measurableSet
    (volume_simplex_pos_of_pos m ha).ne' (volume_simplex_ne_top m a)

theorem differentialEntropy_uniformSimplex (m : ℕ) {a : ℝ} (ha : 0 < a) :
    differentialEntropy (uniformDensity (simplex m a)) volume =
      (m : ℝ) * Real.log a + Real.log (volume (simplex m 1)).toReal := by
  rw [differentialEntropy_uniformDensity (isClosed_simplex m a).measurableSet
    (volume_simplex_pos_of_pos m ha).ne' (volume_simplex_ne_top m a),
    volume_simplex_pos m ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha.le m),
    Real.log_mul (pow_ne_zero _ ha.ne')
      (ENNReal.toReal_ne_zero.mpr ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩),
    Real.log_pow]

end EntropicRogersShephard
