import EntropicRogersShephard.FiberEntropy

/-! Fubini gives the simplex-mixture formula for the actual lifted difference density. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def fiberDifferenceDensity {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  ∫ p, fiberUniformDensity K ρ p * fiberUniformDensity K ρ (p - z)

theorem fiberUniformDensity_le {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    fiberUniformDensity K ρ p ≤ (volume (fiberBody n m K ρ)).toReal⁻¹ := by
  by_cases hp : p ∈ fiberBody n m K ρ
  · simp [fiberUniformDensity, hp]
  · simp only [fiberUniformDensity, Set.indicator_of_notMem hp]
    positivity

theorem integrable_fiberDifference_slice {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C)
    (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    Integrable (fun p => fiberUniformDensity K ρ p * fiberUniformDensity K ρ (p - z)) volume := by
  have hm := measurable_fiberUniformDensity (m := m) hK hρ
  have hi := (integrable_fiberUniformDensity (m := m) hK hfin hρ hc hC hb).mul_const
    (volume (fiberBody n m K ρ)).toReal⁻¹
  apply hi.mono' (hm.mul (hm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change ‖fiberUniformDensity K ρ p * fiberUniformDensity K ρ (p - z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fiberUniformDensity_nonneg K ρ p)
    (fiberUniformDensity_nonneg K ρ (p - z)))]
  exact mul_le_mul_of_nonneg_left (fiberUniformDensity_le K ρ (p - z))
    (fiberUniformDensity_nonneg K ρ p)

theorem measurable_fiberDifferenceDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    Measurable (fiberDifferenceDensity (m := m) K ρ) := by
  have hm := measurable_fiberUniformDensity (m := m) hK hρ
  have h : Measurable (fun p : ((Fin n → ℝ) × (Fin m → ℝ)) ×
      ((Fin n → ℝ) × (Fin m → ℝ)) =>
      fiberUniformDensity K ρ p.2 * fiberUniformDensity K ρ (p.2 - p.1)) :=
    (hm.comp measurable_snd).mul (hm.comp (measurable_snd.sub measurable_fst))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem fiberDifferenceDensity_nonneg {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    0 ≤ fiberDifferenceDensity K ρ z :=
  integral_nonneg fun p => mul_nonneg (fiberUniformDensity_nonneg K ρ p)
    (fiberUniformDensity_nonneg K ρ (p - z))

theorem fiberDifferenceDensity_eq_mixture {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C)
    (s : Fin n → ℝ) (t : Fin m → ℝ) :
    fiberDifferenceDensity K ρ (s, t) =
      ∫ x, powerDensity m K ρ x * powerDensity m K ρ (x - s) *
        crossDifferenceDensity (uniformDensity (simplex m (ρ x)))
          (uniformDensity (simplex m (ρ (x - s)))) t := by
  rw [fiberDifferenceDensity, Measure.volume_eq_prod,
    integral_prod _ (integrable_fiberDifference_slice hK hfin hρ hc hC hb (s, t))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  have he : (fun y : Fin m → ℝ =>
      fiberUniformDensity K ρ (x, y) * fiberUniformDensity K ρ ((x, y) - (s, t))) =
      (fun y => (powerDensity m K ρ x * powerDensity m K ρ (x - s)) *
        (uniformDensity (simplex m (ρ x)) y *
          uniformDensity (simplex m (ρ (x - s))) (y - t))) := by
    funext y
    rw [fiberUniformDensity_factorization hK hfin hpos hρ hc hC hb,
      fiberUniformDensity_factorization hK hfin hpos hρ hc hC hb]
    change (powerDensity m K ρ x * uniformDensity (simplex m (ρ x)) y) *
      (powerDensity m K ρ (x - s) * uniformDensity (simplex m (ρ (x - s))) (y - t)) = _
    ring
  rw [he, integral_const_mul]
  rfl

end EntropicRogersShephard
