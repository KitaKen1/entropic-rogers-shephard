import EntropicRogersShephard.FiberVolume
import EntropicRogersShephard.BoundedDensity

/-! The actual uniform fiber density, its marginal and the original lift entropy. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def fiberUniformDensity {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
  (fiberBody n m K ρ).indicator (fun _ => (volume (fiberBody n m K ρ)).toReal⁻¹)

theorem measurable_fiberUniformDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    Measurable (fiberUniformDensity (m := m) K ρ) :=
  measurable_const.indicator (measurableSet_fiberBody hK hρ)

theorem fiberUniformDensity_nonneg {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    0 ≤ fiberUniformDensity K ρ p := by
  apply Set.indicator_nonneg
  intro _ _
  positivity

theorem integrable_fiberUniformDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fiberUniformDensity (m := m) K ρ) volume := by
  rw [fiberUniformDensity, integrable_indicator_iff (measurableSet_fiberBody hK hρ)]
  have hf : volume (fiberBody n m K ρ) ≠ ∞ := by
    rw [volume_fiberBody hK hfin hρ hc hC hb]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_simplex_ne_top m 1)
  exact integrableOn_const hf

theorem integral_fiberUniformDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    (∫ p, fiberUniformDensity (m := m) K ρ p) = 1 := by
  have hv : (volume (fiberBody n m K ρ)).toReal ≠ 0 := by
    rw [volume_fiberBody_real hK hfin hρ hc hC hb]
    exact mul_ne_zero (powerMass_pos hK hfin hpos hρ hc hC hb).ne'
      (ENNReal.toReal_ne_zero.mpr ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩)
  rw [fiberUniformDensity, integral_indicator_const _ (measurableSet_fiberBody hK hρ),
    smul_eq_mul]
  exact mul_inv_cancel₀ hv

theorem fiberUniformDensity_factorization {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    fiberUniformDensity K ρ p =
      powerDensity m K ρ p.1 * uniformDensity (simplex m (ρ p.1)) p.2 := by
  by_cases hx : p.1 ∈ K
  · by_cases hy : p.2 ∈ simplex m (ρ p.1)
    · have hr := hc.trans_le (hb p.1 hx).1
      have hZ := (powerMass_pos (m := m) hK hfin hpos hρ hc hC hb).ne'
      have hV := ENNReal.toReal_ne_zero.mpr
        ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
      have hp : p ∈ fiberBody n m K ρ := ⟨hx, hy⟩
      simp only [fiberUniformDensity, Set.indicator_of_mem hp, powerDensity,
        powerWeight, Set.indicator_of_mem hx, uniformDensity, Set.indicator_of_mem hy]
      rw [volume_fiberBody_real hK hfin hρ hc hC hb,
        volume_simplex_pos m hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le m)]
      field_simp [hZ, hV, pow_ne_zero m hr.ne']
    · have hp : p ∉ fiberBody n m K ρ := fun hp => hy hp.2
      simp [fiberUniformDensity, hp, uniformDensity, hy]
  · have hp : p ∉ fiberBody n m K ρ := fun hp => hx hp.1
    simp [fiberUniformDensity, hp, powerDensity_eq_zero_of_not_mem hx]

theorem fiberUniformDensity_marginal {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C)
    (x : Fin n → ℝ) :
    (∫ y : Fin m → ℝ, fiberUniformDensity K ρ (x, y)) = powerDensity m K ρ x := by
  simp_rw [fiberUniformDensity_factorization hK hfin hpos hρ hc hC hb]
  rw [integral_const_mul]
  by_cases hx : x ∈ K
  · rw [(isProbabilityDensity_uniformSimplex m (hc.trans_le (hb x hx).1)).2.2.2, mul_one]
  · simp [powerDensity_eq_zero_of_not_mem hx]

theorem integrable_negMulLog_fiberUniformDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fun p => Real.negMulLog (fiberUniformDensity (m := m) K ρ p)) volume := by
  have hf : volume (fiberBody n m K ρ) ≠ ∞ := by
    rw [volume_fiberBody hK hfin hρ hc hC hb]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_simplex_ne_top m 1)
  apply integrable_negMulLog_of_bounded_support (measurableSet_fiberBody hK hρ) hf
    (measurable_fiberUniformDensity hK hρ) (C := (volume (fiberBody n m K ρ)).toReal⁻¹)
  · intro p
    refine ⟨fiberUniformDensity_nonneg K ρ p, ?_⟩
    by_cases hp : p ∈ fiberBody n m K ρ
    · simp [fiberUniformDensity, hp]
    · simp only [fiberUniformDensity, Set.indicator_of_notMem hp]
      positivity
  · intro p hp
    simp [fiberUniformDensity, hp]

theorem differentialEntropy_fiberUniformDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    differentialEntropy (fiberUniformDensity (m := m) K ρ) volume =
      differentialEntropy (powerDensity m K ρ) volume + Real.log (volume (simplex m 1)).toReal +
        (m : ℝ) * ∫ x, powerDensity m K ρ x * Real.log (ρ x) := by
  have hZ := (powerMass_pos (m := m) hK hfin hpos hρ hc hC.le hb).ne'
  have hV := ENNReal.toReal_ne_zero.mpr
    ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
  have hv : (volume (fiberBody n m K ρ)).toReal ≠ 0 := by
    rw [volume_fiberBody_real hK hfin hρ hc hC.le hb]
    exact mul_ne_zero hZ hV
  have he : (fun p => Real.negMulLog (fiberUniformDensity (m := m) K ρ p)) =
      (fiberBody n m K ρ).indicator
        (fun _ => Real.negMulLog (volume (fiberBody n m K ρ)).toReal⁻¹) := by
    funext p
    by_cases hp : p ∈ fiberBody n m K ρ <;> simp [fiberUniformDensity, hp]
  have hh : differentialEntropy (fiberUniformDensity (m := m) K ρ) volume =
      Real.log (volume (fiberBody n m K ρ)).toReal := by
    rw [differentialEntropy, he,
      integral_indicator_const _ (measurableSet_fiberBody hK hρ), smul_eq_mul]
    simp only [Real.negMulLog_def, Real.log_inv, measureReal_def]
    field_simp
  rw [hh, volume_fiberBody_real hK hfin hρ hc hC.le hb, Real.log_mul hZ hV,
    differentialEntropy_powerDensity hK hfin hpos hρ hc hC hb]
  ring

theorem integrable_negMulLog_powerDifferenceDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : IsCompact K)
    (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fun s => Real.negMulLog (differenceDensity (powerDensity m K ρ) s)) volume := by
  have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le hb
  apply integrable_negMulLog_differenceDensity_of_bounded_support hK hf
  · intro x
    exact ⟨hf.2.1 x, powerDensity_le
      (powerMass_pos hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le hb) hC.le
      (fun x hx => ⟨hc.le.trans (hb x hx).1, (hb x hx).2⟩) x⟩
  · exact fun _ hx => powerDensity_eq_zero_of_not_mem hx

end EntropicRogersShephard
