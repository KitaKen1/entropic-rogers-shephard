import EntropicRogersShephard.MixtureMass
import EntropicRogersShephard.SimplexScaling

/-! A measurable family of actual simplex-difference densities with a common bound and support. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def simplexFiberKernel {n : ℕ} (m : ℕ) (ρ : (Fin n → ℝ) → ℝ)
    (s x : Fin n → ℝ) (t : Fin m → ℝ) : ℝ :=
  crossDifferenceDensity (uniformDensity (simplex m (ρ x)))
    (uniformDensity (simplex m (ρ (x - s)))) t

theorem measurable_simplexFiberKernel {n m : ℕ} [NeZero m] {ρ : (Fin n → ℝ) → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 < ρ x) (s : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => simplexFiberKernel m ρ s p.1 p.2) := by
  have he : (fun p : (Fin n → ℝ) × (Fin m → ℝ) => simplexFiberKernel m ρ s p.1 p.2) =
      (fun p => overlapRadius (ρ p.1) (ρ (p.1 - s)) p.2 ^ m /
        (ρ p.1 ^ m * ρ (p.1 - s) ^ m * (volume (simplex m 1)).toReal)) := by
    funext p
    exact crossDifferenceDensity_uniformSimplex m (hp p.1) (hp (p.1 - s)) p.2
  have hr : Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      overlapRadius (ρ p.1) (ρ (p.1 - s)) p.2) := by
    unfold overlapRadius rawRadius
    exact measurable_const.max (((hm.comp measurable_fst).sub
      ((continuous_positiveMass m).measurable.comp measurable_snd)).min
      ((hm.comp (measurable_fst.sub measurable_const)).sub
        ((continuous_negativeMass m).measurable.comp measurable_snd)))
  rw [he]
  exact (hr.pow_const m).div (((hm.comp measurable_fst).pow_const m).mul
    ((hm.comp (measurable_fst.sub measurable_const)).pow_const m) |>.mul_const _)

theorem simplexFiberKernel_nonneg {n m : ℕ} (ρ : (Fin n → ℝ) → ℝ)
    (s x : Fin n → ℝ) (t : Fin m → ℝ) : 0 ≤ simplexFiberKernel m ρ s x t :=
  crossDifferenceDensity_nonneg (uniformDensity_nonneg _) (uniformDensity_nonneg _) t

theorem simplexFiberKernel_le {n m : ℕ} [NeZero m] {ρ : (Fin n → ℝ) → ℝ}
    {c : ℝ} (hc : 0 < c) (hb : ∀ x, c ≤ ρ x)
    (s x : Fin n → ℝ) (t : Fin m → ℝ) :
    simplexFiberKernel m ρ s x t ≤ 1 / (c ^ m * (volume (simplex m 1)).toReal) := by
  have hv : 0 < (volume (simplex m 1)).toReal :=
    ENNReal.toReal_pos (volume_unit_simplex_pos m).ne' (volume_simplex_ne_top m 1)
  calc
    simplexFiberKernel m ρ s x t ≤ 1 / (ρ x ^ m * (volume (simplex m 1)).toReal) :=
      crossDifferenceDensity_uniformSimplex_le m (hc.trans_le (hb x)) (hc.trans_le (hb (x - s))) t
    _ ≤ 1 / (c ^ m * (volume (simplex m 1)).toReal) :=
      one_div_le_one_div_of_le (mul_pos (pow_pos hc m) hv)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le (hb x) m) hv.le)

theorem uniformSimplexDensity_zero_outside_larger_simplex {m : ℕ} {a C : ℝ}
    (ha : a ≤ C) {y : Fin m → ℝ} (hy : y ∉ simplex m C) :
    uniformDensity (simplex m a) y = 0 := by
  have hn : y ∉ simplex m a := fun h => hy ⟨h.1, h.2.trans ha⟩
  simp [uniformDensity, hn]

theorem simplexFiberKernel_zero_outside_common_support {n m : ℕ}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hb : ∀ x, ρ x ≤ C)
    (s x : Fin n → ℝ) {t : Fin m → ℝ}
    (ht : t ∉ bodyDifferenceSupport (simplex m C)) : simplexFiberKernel m ρ s x t = 0 := by
  exact crossDifferenceDensity_eq_zero_of_not_mem_support
    (fun _ hy => uniformSimplexDensity_zero_outside_larger_simplex (hb x) hy)
    (fun _ hy => uniformSimplexDensity_zero_outside_larger_simplex (hb (x - s)) hy) ht

theorem isProbabilityDensity_simplexFiberKernel {n m : ℕ} {ρ : (Fin n → ℝ) → ℝ}
    (hp : ∀ x, 0 < ρ x) (s x : Fin n → ℝ) :
    IsProbabilityDensity m (simplexFiberKernel m ρ s x) :=
  isProbabilityDensity_crossDifferenceDensity (isProbabilityDensity_uniformSimplex m (hp x))
    (isProbabilityDensity_uniformSimplex m (hp (x - s)))

theorem isProbabilityDensity_simplex_mixture {n m : ℕ} [NeZero m]
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {ρ : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) :
    IsProbabilityDensity m (fun t => ∫ x, simplexFiberKernel m ρ s x t ∂μ) := by
  have hp : ∀ x, 0 < ρ x := fun x => hc.trans_le (hb x).1
  have hme := measurable_simplexFiberKernel (m := m) hm hp s
  have hbb : ∀ x t, simplexFiberKernel m ρ s x t ∈
      Icc (0 : ℝ) (1 / (c ^ m * (volume (simplex m 1)).toReal)) :=
    fun x t => ⟨simplexFiberKernel_nonneg ρ s x t, simplexFiberKernel_le hc (fun x => (hb x).1) s x t⟩
  have hT := isCompact_bodyDifferenceSupport (isCompact_simplex m C)
  have hsupp : ∀ x t, t ∉ bodyDifferenceSupport (simplex m C) → simplexFiberKernel m ρ s x t = 0 :=
    fun x _ ht => simplexFiberKernel_zero_outside_common_support (fun x => (hb x).2) s x ht
  exact ⟨hme.stronglyMeasurable.integral_prod_left'.measurable,
    fun t => integral_nonneg (fun x => simplexFiberKernel_nonneg ρ s x t),
    integrable_kernel_mixture_of_bounded_support hme hbb hT.measurableSet hT.measure_ne_top hsupp,
    integral_kernel_mixture_of_bounded_support hme hbb hT.measurableSet hT.measure_ne_top hsupp
      (fun x => (isProbabilityDensity_simplexFiberKernel hp s x).2.2.2)⟩

theorem average_entropy_le_simplex_mixture_entropy {n m : ℕ} [NeZero m]
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {ρ : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hm : Measurable ρ) (hc : 0 < c) (hb : ∀ x, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) :
    (∫ x, differentialEntropy (simplexFiberKernel m ρ s x) volume ∂μ) ≤
      differentialEntropy (fun t => ∫ x, simplexFiberKernel m ρ s x t ∂μ) volume := by
  have hp : ∀ x, 0 < ρ x := fun x => hc.trans_le (hb x).1
  have hbb : ∀ x t, simplexFiberKernel m ρ s x t ∈
      Icc (0 : ℝ) (1 / (c ^ m * (volume (simplex m 1)).toReal)) :=
    fun x t => ⟨simplexFiberKernel_nonneg ρ s x t, simplexFiberKernel_le hc (fun x => (hb x).1) s x t⟩
  have hT := isCompact_bodyDifferenceSupport (isCompact_simplex m C)
  exact average_entropy_le_entropy_bounded_mixture (measurable_simplexFiberKernel (m := m) hm hp s)
    hbb hT.measurableSet hT.measure_ne_top
    (fun x _ ht => simplexFiberKernel_zero_outside_common_support (fun x => (hb x).2) s x ht)

end EntropicRogersShephard
