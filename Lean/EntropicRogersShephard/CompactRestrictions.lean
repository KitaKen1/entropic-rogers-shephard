import EntropicRogersShephard.LocalLogConcave
import EntropicRogersShephard.DominatedConvolution

/-! Normalize an increasing exhaustion only after its mass is bounded below. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem compact_restrictions_approximation {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    ∃ K : ℕ → Set (Fin n → ℝ),
      (∀ j, IsCompact (K j)) ∧ (∀ j, Convex ℝ (K j)) ∧
      (∀ j, K j ⊆ interior {x | 0 < f x}) ∧ (∀ j, volume (K j) ≠ 0) ∧
      (∀ j, IsProbabilityDensity n (powerDensity 1 (K j) f)) ∧
      (∀ j x, powerDensity 1 (K j) f x ≤ 2 * f x) ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => powerDensity 1 (K j) f x) atTop (𝓝 (f x))) := by
  obtain ⟨K, hmono, hcomp, hconv, hsub, hcover, hae⟩ :=
    compact_convex_exhaustion (convex_positiveSet_of_isLogConcave hl)
  have hwlim : ∀ᵐ x ∂volume, Tendsto (fun j => powerWeight 1 (K j) f x) atTop (𝓝 (f x)) := by
    filter_upwards [hae] with x hx
    by_cases hp : 0 < f x
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hx.mpr hp)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with j hj
      simp [powerWeight, hmono hj hi]
    · have hz : f x = 0 := le_antisymm (not_lt.mp hp) (hf.2.1 x)
      have he : (fun j => powerWeight 1 (K j) f x) = fun _ => 0 := by
        funext j
        simp [powerWeight, hz]
      rw [hz, he]
      exact tendsto_const_nhds
  have hwle : ∀ j x, powerWeight 1 (K j) f x ≤ f x := by
    intro j x
    by_cases hx : x ∈ K j
    · simp [powerWeight, hx]
    · simpa [powerWeight, hx] using hf.2.1 x
  have hwint : ∀ j, Integrable (powerWeight 1 (K j) f) volume := by
    intro j
    simpa only [powerWeight, pow_one] using hf.2.2.1.indicator (hcomp j).measurableSet
  have hZ : Tendsto (fun j => powerMass 1 (K j) f) atTop (𝓝 (1 : ℝ)) := by
    rw [← hf.2.2.2]
    apply tendsto_integral_of_dominated_convergence f
      (fun j => (measurable_powerWeight (hcomp j).measurableSet hf.1).aestronglyMeasurable)
      hf.2.2.1
    · intro j
      exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (powerWeight_nonneg (fun x _ => hf.2.1 x) x)]
        exact hwle j x)
    · exact hwlim
  obtain ⟨J, hmass⟩ := positive_mass_lower_after_shift (by norm_num : (0 : ℝ) < 1) hZ
  have hmasspos (j : ℕ) : 0 < powerMass 1 (K (j + J)) f :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hmass j)
  have hpos (j : ℕ) : volume (K (j + J)) ≠ 0 := by
    intro hz
    have he : powerMass 1 (K (j + J)) f = 0 := by
      simp only [powerMass, powerWeight, pow_one]
      rw [integral_indicator (hcomp _).measurableSet, Measure.restrict_zero_set hz,
        integral_zero_measure]
    linarith [hmasspos j]
  have hd (j : ℕ) : IsProbabilityDensity n (powerDensity 1 (K (j + J)) f) :=
    ⟨measurable_powerDensity (hcomp _).measurableSet hf.1,
      powerDensity_nonneg (fun x _ => hf.2.1 x), integrable_powerDensity (hwint _),
      integral_powerDensity (hmasspos j).ne'⟩
  refine ⟨fun j => K (j + J), fun j => hcomp _, fun j => hconv _, fun j => hsub _, hpos,
    hd, ?_, ?_⟩
  · intro j x
    change powerWeight 1 (K (j + J)) f x / powerMass 1 (K (j + J)) f ≤ 2 * f x
    apply (div_le_iff₀ (hmasspos j)).mpr
    have hz := hmass j
    have hnn := hf.2.1 x
    nlinarith [hwle (j + J) x]
  · have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
    filter_upwards [hwlim] with x hx
    have h := (hx.comp hshift).div (hZ.comp hshift) (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun j => powerWeight 1 (K (j + J)) f x /
      powerMass 1 (K (j + J)) f) atTop (𝓝 (f x / 1)) at h
    simpa only [powerDensity, div_one] using h

end EntropicRogersShephard
