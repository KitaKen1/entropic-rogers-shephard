import EntropicRogersShephard.DensityMeasure

/-! Bounded common supports discharge the entropy-mixture integrability conditions. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem integrable_kernel_slice_of_bounded {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : α → β → ℝ} {M : ℝ} (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M) (b : β) :
    Integrable (fun a => κ a b) μ := by
  have hme : Measurable (fun a => κ a b) := hm.comp (measurable_id.prodMk measurable_const)
  apply (integrable_const M).mono' hme.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (hb a b).1]
  exact (hb a b).2

theorem integrable_negMulLog_kernel_slice_of_bounded {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : α → β → ℝ} {M : ℝ} (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M) (b : β) :
    Integrable (fun a => Real.negMulLog (κ a b)) μ := by
  obtain ⟨L, _, hL⟩ := exists_negMulLog_bound M
  have hme : Measurable (fun a => κ a b) := hm.comp (measurable_id.prodMk measurable_const)
  apply (integrable_const L).mono' (Real.continuous_negMulLog.measurable.comp hme).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => hL _ (hb a b)

theorem integrable_negMulLog_kernel_prod_of_bounded_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0) :
    Integrable (fun p : α × β => Real.negMulLog (κ p.1 p.2)) (μ.prod ν) := by
  have hfp : (μ.prod ν) (univ ×ˢ S) ≠ ∞ := by
    simpa only [Measure.prod_prod, measure_univ, one_mul] using hfin
  apply integrable_negMulLog_of_bounded_support (MeasurableSet.univ.prod hs)
    (s := univ ×ˢ S) (C := M) hfp hm (fun p => hb p.1 p.2)
  intro p hp
  exact hsupp p.1 p.2 (by simpa only [Set.mem_prod, Set.mem_univ, true_and] using hp)

theorem integrable_entropy_kernel_of_bounded_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0) :
    Integrable (fun a => differentialEntropy (κ a) ν) μ :=
  (integrable_negMulLog_kernel_prod_of_bounded_support hm hb hs hfin hsupp).integral_prod_left

theorem average_entropy_le_entropy_bounded_mixture {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0) :
    (∫ a, differentialEntropy (κ a) ν ∂μ) ≤
      differentialEntropy (fun b => ∫ a, κ a b ∂μ) ν := by
  have hmixed : Measurable (fun b => ∫ a, κ a b ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have hmixint : Integrable (fun b => Real.negMulLog (∫ a, κ a b ∂μ)) ν := by
    apply integrable_negMulLog_of_bounded_support hs hfin hmixed (C := M)
    · intro b
      refine ⟨integral_nonneg (fun a => (hb a b).1), ?_⟩
      have h : (∫ a, κ a b ∂μ) ≤ ∫ _ : α, M ∂μ :=
        integral_mono (integrable_kernel_slice_of_bounded (μ := μ) hm hb b)
        (integrable_const M) (fun a => (hb a b).2)
      simpa using h
    · intro b hbs
      simp only [hsupp _ b hbs, integral_zero]
  exact average_entropy_le_entropy_mixture
    (fun b => Filter.Eventually.of_forall (fun a => (hb a b).1))
    (integrable_kernel_slice_of_bounded hm hb)
    (integrable_negMulLog_kernel_slice_of_bounded hm hb)
    (integrable_negMulLog_kernel_prod_of_bounded_support hm hb hs hfin hsupp) hmixint

theorem integrable_negMulLog_const_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ)
    (he : Integrable (fun x => Real.negMulLog (f x)) μ) (c : ℝ) :
    Integrable (fun x => Real.negMulLog (c * f x)) μ := by
  have heq : (fun x => Real.negMulLog (c * f x)) =
      (fun x => c * Real.negMulLog (f x) + Real.negMulLog c * f x) := by
    funext x
    rw [Real.negMulLog_mul]
    ring
  rw [heq]
  exact (he.const_mul c).add (hf.const_mul (Real.negMulLog c))

theorem differentialEntropy_const_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hm : (∫ x, f x ∂μ) = 1)
    (he : Integrable (fun x => Real.negMulLog (f x)) μ) (c : ℝ) :
    differentialEntropy (fun x => c * f x) μ =
      c * differentialEntropy f μ + Real.negMulLog c := by
  have heq : (fun x => Real.negMulLog (c * f x)) =
      (fun x => c * Real.negMulLog (f x) + Real.negMulLog c * f x) := by
    funext x
    rw [Real.negMulLog_mul]
    ring
  rw [differentialEntropy, heq, integral_add (he.const_mul c) (hf.const_mul _), integral_const_mul, integral_const_mul,
    hm, mul_one]
  rfl

end EntropicRogersShephard
