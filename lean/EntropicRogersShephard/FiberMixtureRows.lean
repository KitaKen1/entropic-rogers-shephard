import EntropicRogersShephard.FiberTransport
import EntropicRogersShephard.SimplexMixtureEntropy

/-! Rowwise entropy lower bounds for the actual fiber difference, including zero-mass rows. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem differenceWeight_ae_zero_of_density_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hf : IsProbabilityDensity n f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) M)
    {s : Fin n → ℝ} (hs : differenceDensity f s = 0) :
    (fun x => f x * f (x - s)) =ᵐ[volume] (fun _ => 0) :=
  (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (hf.2.1 x) (hf.2.1 (x - s)))
    (integrable_difference_slice_of_bounded hf hf.1 hb s)).mp hs

theorem integral_differenceWeight_mul_eq_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hf : IsProbabilityDensity n f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) M)
    {s : Fin n → ℝ} (hs : differenceDensity f s = 0) (g : (Fin n → ℝ) → ℝ) :
    (∫ x, f x * f (x - s) * g x) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [differenceWeight_ae_zero_of_density_zero hf hb hs] with x hx
  change f x * f (x - s) = 0 at hx
  change f x * f (x - s) * g x = 0
  rw [hx, zero_mul]

theorem fiberDifferenceDensity_eq_slice_mixture {n m : ℕ} [NeZero m]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C)
    {s : Fin n → ℝ} (hs : 0 < differenceDensity (powerDensity m K ρ) s) (t : Fin m → ℝ) :
    fiberDifferenceDensity K ρ (s, t) = differenceDensity (powerDensity m K ρ) s *
      ∫ x, simplexFiberKernel m ρ s x t ∂differenceSliceMeasure (powerDensity m K ρ) s := by
  have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have he : (∫ x, simplexFiberKernel m ρ s x t ∂differenceSliceMeasure (powerDensity m K ρ) s) =
      fiberDifferenceDensity K ρ (s, t) / differenceDensity (powerDensity m K ρ) s := by
    rw [integral_differenceSliceMeasure hf.1 hf.2.1,
      fiberDifferenceDensity_eq_mixture hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
        (fun x _ => hb x)]
    rfl
  rw [he]
  field_simp [hs.ne']

theorem fiberDifferenceDensity_zero_of_powerDifference_zero {n m : ℕ}
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C)
    {s : Fin n → ℝ} (hs : differenceDensity (powerDensity m K ρ) s = 0) (t : Fin m → ℝ) :
    fiberDifferenceDensity K ρ (s, t) = 0 := by
  have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have hZ := powerMass_pos (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have hfB : ∀ x, powerDensity m K ρ x ∈ Icc (0 : ℝ) (C ^ m / powerMass m K ρ) :=
    fun x => ⟨hf.2.1 x, powerDensity_le hZ hC.le (fun x _ => ⟨hc.le.trans (hb x).1, (hb x).2⟩) x⟩
  rw [fiberDifferenceDensity_eq_mixture hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)]
  exact integral_differenceWeight_mul_eq_zero hf hfB hs (fun x => simplexFiberKernel m ρ s x t)

theorem fiber_row_entropy_lower_bound_of_pos {n m : ℕ} [NeZero m]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C)
    {s : Fin n → ℝ} (hs : 0 < differenceDensity (powerDensity m K ρ) s) :
    Real.negMulLog (differenceDensity (powerDensity m K ρ) s) +
      differenceDensity (powerDensity m K ρ) s *
        differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
          (uniformDensity (simplex m 1))) volume +
      (m : ℝ) / 2 * ((∫ x, powerDensity m K ρ x * powerDensity m K ρ (x - s) * Real.log (ρ x)) +
        (∫ x, powerDensity m K ρ x * powerDensity m K ρ (x - s) * Real.log (ρ (x - s)))) ≤
        differentialEntropy (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) volume := by
  let f := powerDensity m K ρ
  let S := differenceDensity f s
  let μ := differenceSliceMeasure f s
  let E := differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
    (uniformDensity (simplex m 1))) volume
  have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have hZ := powerMass_pos (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have hfB : ∀ x, f x ∈ Icc (0 : ℝ) (C ^ m / powerMass m K ρ) :=
    fun x => ⟨hf.2.1 x, powerDensity_le hZ hC.le (fun x _ => ⟨hc.le.trans (hb x).1, (hb x).2⟩) x⟩
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_differenceSliceMeasure hf hfB hs
  let N := fun t => ∫ x, simplexFiberKernel m ρ s x t ∂μ
  have hprob := isProbabilityDensity_simplex_mixture (m := m) (μ := μ) hρ hc hb s
  have hent := integrable_negMulLog_simplex_mixture (m := m) (μ := μ) hρ hc hb s
  have hlow := simplex_mixture_entropy_scale_lower_bound (m := m) (μ := μ) hρ hc hb s
  change E + (m : ℝ) / 2 *
    ((∫ x, Real.log (ρ x) ∂differenceSliceMeasure f s) +
      (∫ x, Real.log (ρ (x - s)) ∂differenceSliceMeasure f s)) ≤
        differentialEntropy N volume at hlow
  rw [integral_differenceSliceMeasure hf.1 hf.2.1, integral_differenceSliceMeasure hf.1 hf.2.1] at hlow
  have he : (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) = (fun t => S * N t) := by
    funext t
    exact fiberDifferenceDensity_eq_slice_mixture hK hpos hρ hc hC hb hs t
  have hchain : differentialEntropy (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) volume =
      S * differentialEntropy N volume + Real.negMulLog S := by
    rw [he]
    exact differentialEntropy_const_mul hprob.2.2.1 hprob.2.2.2 hent S
  have hscale := mul_le_mul_of_nonneg_left hlow hs.le
  have hS : S ≠ 0 := hs.ne'
  have halg (A B : ℝ) : S * (E + (m : ℝ) / 2 * (A / S + B / S)) =
      S * E + (m : ℝ) / 2 * (A + B) := by
    field_simp [hS]
    <;> ring
  change S * (E + (m : ℝ) / 2 *
    ((∫ x, f x * f (x - s) * Real.log (ρ x)) / S +
      (∫ x, f x * f (x - s) * Real.log (ρ (x - s))) / S)) ≤ S * differentialEntropy N volume at hscale
  rw [halg] at hscale
  change Real.negMulLog S + S * E + (m : ℝ) / 2 *
    ((∫ x, f x * f (x - s) * Real.log (ρ x)) +
      (∫ x, f x * f (x - s) * Real.log (ρ (x - s)))) ≤ _
  rw [hchain]
  exact (by simpa only [add_assoc, add_comm, add_left_comm] using
    add_le_add_left hscale (Real.negMulLog S))

theorem fiber_row_entropy_lower_bound {n m : ℕ} [NeZero m]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C) (s : Fin n → ℝ) :
    Real.negMulLog (differenceDensity (powerDensity m K ρ) s) +
      differenceDensity (powerDensity m K ρ) s *
        differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
          (uniformDensity (simplex m 1))) volume +
      (m : ℝ) / 2 * ((∫ x, powerDensity m K ρ x * powerDensity m K ρ (x - s) * Real.log (ρ x)) +
        (∫ x, powerDensity m K ρ x * powerDensity m K ρ (x - s) * Real.log (ρ (x - s)))) ≤
        differentialEntropy (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) volume := by
  by_cases hs : 0 < differenceDensity (powerDensity m K ρ) s
  · exact fiber_row_entropy_lower_bound_of_pos hK hpos hρ hc hC hb hs
  · have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
      (fun x _ => hb x)
    have hZ := powerMass_pos (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
      (fun x _ => hb x)
    have hfB : ∀ x, powerDensity m K ρ x ∈ Icc (0 : ℝ) (C ^ m / powerMass m K ρ) :=
      fun x => ⟨hf.2.1 x, powerDensity_le hZ hC.le (fun x _ => ⟨hc.le.trans (hb x).1, (hb x).2⟩) x⟩
    have hs0 : differenceDensity (powerDensity m K ρ) s = 0 :=
      le_antisymm (not_lt.mp hs) (crossDifferenceDensity_nonneg hf.2.1 hf.2.1 s)
    have ha := integral_differenceWeight_mul_eq_zero hf hfB hs0 (fun x => Real.log (ρ x))
    have hb' := integral_differenceWeight_mul_eq_zero hf hfB hs0 (fun x => Real.log (ρ (x - s)))
    have hz : (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) = (fun _ => 0) := by
      funext t
      exact fiberDifferenceDensity_zero_of_powerDifference_zero hK hpos hρ hc hC hb hs0 t
    rw [hz]
    simp only [hs0, ha, hb', Real.negMulLog_zero, zero_mul, zero_add, add_zero, mul_zero,
      differentialEntropy, integral_zero, le_refl]

end EntropicRogersShephard
