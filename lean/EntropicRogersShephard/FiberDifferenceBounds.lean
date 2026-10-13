import EntropicRogersShephard.FiberDifference

/-! Compact support, pointwise bounds and finite entropy of the actual lifted difference. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

def fiberDifferenceSupport {n m : ℕ} (K : Set (Fin n → ℝ)) (ρ : (Fin n → ℝ) → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  (fun p : ((Fin n → ℝ) × (Fin m → ℝ)) × ((Fin n → ℝ) × (Fin m → ℝ)) =>
    p.1 - p.2) '' (fiberBody n m K ρ ×ˢ fiberBody n m K ρ)

theorem isCompact_fiberDifferenceSupport {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hK : IsCompact K) (hρ : ContinuousOn ρ K)
    (hb : ∀ x ∈ K, ρ x ≤ C) : IsCompact (fiberDifferenceSupport (m := m) K ρ) := by
  have hB := isCompact_fiberBody (m := m) hK hρ hb
  exact (hB.prod hB).image (continuous_fst.sub continuous_snd)

theorem fiberDifferenceDensity_eq_zero_of_not_mem {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {z : (Fin n → ℝ) × (Fin m → ℝ)}
    (hz : z ∉ fiberDifferenceSupport K ρ) : fiberDifferenceDensity K ρ z = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p ∈ fiberBody n m K ρ
  · have hq : p - z ∉ fiberBody n m K ρ := by
      intro hq
      exact hz ⟨(p, p - z), ⟨hp, hq⟩, by simp⟩
    simp [fiberUniformDensity, hq]
  · simp [fiberUniformDensity, hp]

theorem fiberDifferenceDensity_le {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C)
    (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    fiberDifferenceDensity K ρ z ≤ (volume (fiberBody n m K ρ)).toReal⁻¹ := by
  have hi := integrable_fiberDifference_slice hK hfin hρ hc hC hb z
  calc
    fiberDifferenceDensity K ρ z ≤
        ∫ p, fiberUniformDensity K ρ p * (volume (fiberBody n m K ρ)).toReal⁻¹ := by
      apply integral_mono hi ((integrable_fiberUniformDensity (m := m) hK hfin hρ hc hC hb).mul_const _)
      intro p
      exact mul_le_mul_of_nonneg_left (fiberUniformDensity_le K ρ (p - z))
        (fiberUniformDensity_nonneg K ρ p)
    _ = (volume (fiberBody n m K ρ)).toReal⁻¹ := by
      rw [integral_mul_const, integral_fiberUniformDensity hK hfin hpos hρ hc hC hb, one_mul]

theorem integrable_negMulLog_fiberDifferenceDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : IsCompact K)
    (hpos : volume K ≠ 0) (hρ : Measurable ρ) (hcont : ContinuousOn ρ K)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fun z => Real.negMulLog (fiberDifferenceDensity (m := m) K ρ z)) volume := by
  have hD := isCompact_fiberDifferenceSupport (m := m) hK hcont (fun x hx => (hb x hx).2)
  apply integrable_negMulLog_of_bounded_support hD.measurableSet hD.measure_ne_top
    (measurable_fiberDifferenceDensity hK.measurableSet hρ)
  · intro z
    exact ⟨fiberDifferenceDensity_nonneg K ρ z,
      fiberDifferenceDensity_le hK.measurableSet hK.measure_ne_top hpos hρ hc hC hb z⟩
  · exact fun _ hz => fiberDifferenceDensity_eq_zero_of_not_mem hz

end EntropicRogersShephard
