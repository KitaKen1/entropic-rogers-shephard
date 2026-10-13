import EntropicRogersShephard.BodyDensity

/-! Pointwise difference-convolution bounds for bounded probability densities. -/

open MeasureTheory Set Real

namespace EntropicRogersShephard

theorem integrable_difference_slice_of_bounded {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {M : ℝ} (hf : IsProbabilityDensity n f)
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) M) (s : Fin n → ℝ) :
    Integrable (fun x => f x * g (x - s)) volume := by
  apply (hf.2.2.1.mul_const M).mono'
    (hf.1.mul (hg.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖f x * g (x - s)‖ ≤ f x * M
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf.2.1 x) (hb _).1)]
  exact mul_le_mul_of_nonneg_left (hb _).2 (hf.2.1 x)

theorem crossDifferenceDensity_le_of_bounded {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {M : ℝ} (hf : IsProbabilityDensity n f)
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) M) (s : Fin n → ℝ) :
    crossDifferenceDensity f g s ≤ M := by
  have hi := integrable_difference_slice_of_bounded hf hg hb s
  calc
    crossDifferenceDensity f g s ≤ ∫ x, f x * M := by
      apply integral_mono hi (hf.2.2.1.mul_const M)
      intro x
      exact mul_le_mul_of_nonneg_left (hb _).2 (hf.2.1 x)
    _ = M := by rw [integral_mul_const, hf.2.2.2, one_mul]

theorem crossDifferenceDensity_eq_zero_of_not_mem_support {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hf : ∀ x ∉ K, f x = 0) (hg : ∀ x ∉ K, g x = 0)
    {s : Fin n → ℝ} (hs : s ∉ bodyDifferenceSupport K) :
    crossDifferenceDensity f g s = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · have hy : x - s ∉ K := by
      intro hy
      exact hs ⟨(x, x - s), ⟨hx, hy⟩, by simp⟩
    simp [hg _ hy]
  · simp [hf _ hx]

theorem integrable_negMulLog_differenceDensity_of_bounded_support {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)} {M : ℝ}
    (hK : IsCompact K) (hf : IsProbabilityDensity n f)
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) M) (hsupp : ∀ x ∉ K, f x = 0) :
    Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume := by
  have hD := isCompact_bodyDifferenceSupport hK
  apply integrable_negMulLog_of_bounded_support hD.measurableSet hD.measure_ne_top
    (measurable_crossDifferenceDensity hf.1 hf.1)
  · intro s
    exact ⟨crossDifferenceDensity_nonneg hf.2.1 hf.2.1 s,
      crossDifferenceDensity_le_of_bounded hf hf.1 hb s⟩
  · exact fun _ hs => crossDifferenceDensity_eq_zero_of_not_mem_support hsupp hsupp hs

end EntropicRogersShephard
