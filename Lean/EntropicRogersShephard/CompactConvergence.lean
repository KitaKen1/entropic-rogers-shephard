import EntropicRogersShephard.BoundedDensity

/-! A common bounded support gives pointwise convolution and difference-entropy convergence. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem differenceDensity_tendsto_of_bounded_support {n : ℕ}
    {K : Set (Fin n → ℝ)} {f : ℕ → (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hK : MeasurableSet K) (hfin : volume K ≠ ∞) (hM : 0 ≤ M)
    (hm : ∀ j, Measurable (f j)) (hb : ∀ j x, f j x ∈ Icc (0 : ℝ) M)
    (hsupp : ∀ j x, x ∉ K → f j x = 0)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x))) (s : Fin n → ℝ) :
    Tendsto (fun j => differenceDensity (f j) s) atTop (𝓝 (differenceDensity g s)) := by
  have hi : Integrable (K.indicator (fun _ : Fin n → ℝ => M ^ 2)) volume := by
    rw [integrable_indicator_iff hK]
    exact integrableOn_const hfin
  apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => M ^ 2))
    (fun j => ((hm j).mul ((hm j).comp (measurable_id.sub measurable_const))).aestronglyMeasurable) hi
  · intro j
    apply Filter.Eventually.of_forall
    intro x
    change ‖f j x * f j (x - s)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb j x).1 (hb j (x - s)).1)]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, pow_two]
      exact mul_le_mul (hb j x).2 (hb j (x - s)).2 (hb j (x - s)).1 hM
    · simp [hx, hsupp j x hx]
  · exact Filter.Eventually.of_forall (fun x => (hlim x).mul (hlim (x - s)))

theorem difference_entropy_tendsto_of_compact_support {n : ℕ}
    {K : Set (Fin n → ℝ)} {f : ℕ → (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hK : IsCompact K) (hM : 0 ≤ M) (hf : ∀ j, IsProbabilityDensity n (f j))
    (hb : ∀ j x, f j x ∈ Icc (0 : ℝ) M) (hsupp : ∀ j x, x ∉ K → f j x = 0)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto (fun j => differentialEntropy (differenceDensity (f j)) volume) atTop
      (𝓝 (differentialEntropy (differenceDensity g) volume)) := by
  have hD := isCompact_bodyDifferenceSupport hK
  apply entropy_tendsto_of_bounded_support hD.measurableSet hD.measure_ne_top
    (fun j => measurable_crossDifferenceDensity (hf j).1 (hf j).1) (C := M)
  · intro j s
    exact ⟨crossDifferenceDensity_nonneg (hf j).2.1 (hf j).2.1 s,
      crossDifferenceDensity_le_of_bounded (hf j) (hf j).1 (hb j) s⟩
  · intro j s hs
    exact crossDifferenceDensity_eq_zero_of_not_mem_support (hsupp j) (hsupp j) hs
  · exact differenceDensity_tendsto_of_bounded_support hK.measurableSet hK.measure_ne_top hM
      (fun j => (hf j).1) hb hsupp hlim

end EntropicRogersShephard
