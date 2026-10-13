import EntropicRogersShephard.SimplexKernel

/-! The all-positive-scale simplex comparison applies to a bounded measurable probability mixture. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem abs_log_le_of_mem_Icc {c C r : ℝ} (hc : 0 < c) (hr : r ∈ Icc c C) :
    |Real.log r| ≤ |Real.log c| + |Real.log C| := by
  have hl := Real.log_le_log hc hr.1
  have hu := Real.log_le_log (hc.trans_le hr.1) hr.2
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log c)
    have := abs_nonneg (Real.log C)
    linarith
  · have := le_abs_self (Real.log C)
    have := abs_nonneg (Real.log c)
    linarith

theorem integrable_log_of_bounded_positive {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {ρ : α → ℝ} {c C : ℝ}
    (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C) :
    Integrable (fun x => Real.log (ρ x)) μ := by
  apply (integrable_const (|Real.log c| + |Real.log C|)).mono' hm.log.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact abs_log_le_of_mem_Icc hc (hb x))

theorem integrable_entropy_simplexFiberKernel {n m : ℕ} [NeZero m]
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {ρ : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) :
    Integrable (fun x => differentialEntropy (simplexFiberKernel m ρ s x) volume) μ := by
  have hp : ∀ x, 0 < ρ x := fun x => hc.trans_le (hb x).1
  have hbb : ∀ x t, simplexFiberKernel m ρ s x t ∈
      Icc (0 : ℝ) (1 / (c ^ m * (volume (simplex m 1)).toReal)) :=
    fun x t => ⟨simplexFiberKernel_nonneg ρ s x t, simplexFiberKernel_le hc (fun x => (hb x).1) s x t⟩
  have hT := isCompact_bodyDifferenceSupport (isCompact_simplex m C)
  exact integrable_entropy_kernel_of_bounded_support (measurable_simplexFiberKernel (m := m) hm hp s)
    hbb hT.measurableSet hT.measure_ne_top
    (fun x _ ht => simplexFiberKernel_zero_outside_common_support (fun x => (hb x).2) s x ht)

theorem integrable_negMulLog_simplex_mixture {n m : ℕ} [NeZero m]
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {ρ : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) :
    Integrable (fun t => Real.negMulLog (∫ x, simplexFiberKernel m ρ s x t ∂μ)) volume := by
  have hprob := isProbabilityDensity_simplex_mixture (m := m) (μ := μ) hm hc hb s
  have hp : ∀ x, 0 < ρ x := fun x => hc.trans_le (hb x).1
  have hbb : ∀ x t, simplexFiberKernel m ρ s x t ∈
      Icc (0 : ℝ) (1 / (c ^ m * (volume (simplex m 1)).toReal)) :=
    fun x t => ⟨simplexFiberKernel_nonneg ρ s x t, simplexFiberKernel_le hc (fun x => (hb x).1) s x t⟩
  have hT := isCompact_bodyDifferenceSupport (isCompact_simplex m C)
  apply integrable_negMulLog_of_bounded_support hT.measurableSet hT.measure_ne_top hprob.1
    (C := 1 / (c ^ m * (volume (simplex m 1)).toReal))
  · intro t
    refine ⟨hprob.2.1 t, ?_⟩
    have h : (∫ x, simplexFiberKernel m ρ s x t ∂μ) ≤
        ∫ _ : Fin n → ℝ, 1 / (c ^ m * (volume (simplex m 1)).toReal) ∂μ :=
      integral_mono (integrable_kernel_slice_of_bounded (μ := μ)
      (measurable_simplexFiberKernel (m := m) hm hp s) hbb t) (integrable_const _)
      (fun x => (hbb x t).2)
    simpa using h
  · intro t ht
    simp only [simplexFiberKernel_zero_outside_common_support (fun x => (hb x).2) s _ ht, integral_zero]

theorem simplex_mixture_entropy_scale_lower_bound {n m : ℕ} [NeZero m]
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {ρ : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
      (uniformDensity (simplex m 1))) volume +
        (m : ℝ) / 2 * ((∫ x, Real.log (ρ x) ∂μ) + (∫ x, Real.log (ρ (x - s)) ∂μ)) ≤
      differentialEntropy (fun t => ∫ x, simplexFiberKernel m ρ s x t ∂μ) volume := by
  have hlog := integrable_log_of_bounded_positive (μ := μ) hm hc hb
  have hshift : Integrable (fun x => Real.log (ρ (x - s))) μ :=
    integrable_log_of_bounded_positive (μ := μ)
    (hm.comp (measurable_id.sub measurable_const)) hc (fun x => hb (x - s))
  let E := differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
    (uniformDensity (simplex m 1))) volume
  have hi : Integrable (fun x => E + (m : ℝ) / 2 *
      (Real.log (ρ x) + Real.log (ρ (x - s)))) μ :=
    (integrable_const E).add ((hlog.add hshift).const_mul _)
  have h := integral_mono hi (integrable_entropy_simplexFiberKernel (m := m) hm hc hb s)
    (fun x => simplex_difference_entropy_scale_bound_all m
      (hc.trans_le (hb x).1) (hc.trans_le (hb (x - s)).1))
  have he : (∫ x, E + (m : ℝ) / 2 * (Real.log (ρ x) + Real.log (ρ (x - s))) ∂μ) =
      E + (m : ℝ) / 2 * ((∫ x, Real.log (ρ x) ∂μ) + (∫ x, Real.log (ρ (x - s)) ∂μ)) := by
    rw [integral_add (f := fun _ : Fin n → ℝ => E)
      (g := fun x => (m : ℝ) / 2 * (Real.log (ρ x) + Real.log (ρ (x - s))))
      (integrable_const E) ((hlog.add hshift).const_mul _),
      integral_const_mul, integral_add (f := fun x => Real.log (ρ x))
        (g := fun x => Real.log (ρ (x - s))) hlog hshift]
    simp
  rw [he] at h
  exact h.trans (average_entropy_le_simplex_mixture_entropy (m := m) hm hc hb s)

end EntropicRogersShephard
