import EntropicRogersShephard.BoundedMixture

/-! Integrability and normalization of bounded common-support mixtures. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem integrable_kernel_prod_of_bounded_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0) :
    Integrable (fun p : α × β => κ p.1 p.2) (μ.prod ν) := by
  have hfp : (μ.prod ν) (univ ×ˢ S) ≠ ∞ := by
    simpa only [Measure.prod_prod, measure_univ, one_mul] using hfin
  have hi : Integrable ((univ ×ˢ S).indicator (fun _ : α × β => M)) (μ.prod ν) := by
    rw [integrable_indicator_iff (MeasurableSet.univ.prod hs)]
    exact integrableOn_const hfp
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (hb p.1 p.2).1]
  by_cases hp : p.2 ∈ S
  · have hpu : p ∈ univ ×ˢ S := ⟨Set.mem_univ _, hp⟩
    rw [Set.indicator_of_mem hpu]
    exact (hb p.1 p.2).2
  · simp [hsupp p.1 p.2 hp, hp]

theorem integrable_kernel_mixture_of_bounded_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0) :
    Integrable (fun b => ∫ a, κ a b ∂μ) ν :=
  (integrable_kernel_prod_of_bounded_support hm hb hs hfin hsupp).integral_prod_right

theorem integral_kernel_mixture_of_bounded_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ} {M : ℝ} {S : Set β}
    (hm : Measurable (fun p : α × β => κ p.1 p.2))
    (hb : ∀ a b, κ a b ∈ Icc (0 : ℝ) M)
    (hs : MeasurableSet S) (hfin : ν S ≠ ∞) (hsupp : ∀ a b, b ∉ S → κ a b = 0)
    (hmass : ∀ a, (∫ b, κ a b ∂ν) = 1) :
    (∫ b, ∫ a, κ a b ∂μ ∂ν) = 1 := by
  calc
    (∫ b, ∫ a, κ a b ∂μ ∂ν) = ∫ a, ∫ b, κ a b ∂ν ∂μ :=
      (integral_integral_swap (integrable_kernel_prod_of_bounded_support hm hb hs hfin hsupp)).symm
    _ = 1 := by simp [hmass]

end EntropicRogersShephard
