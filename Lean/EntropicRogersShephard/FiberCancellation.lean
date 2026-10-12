import EntropicRogersShephard.FiberMixtureRows

/-! Signed log moments are ordinary cross-difference convolutions; their masses cancel the fibers. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def differenceLogLeft {n : ℕ} (f ρ : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) : ℝ :=
  ∫ x, f x * f (x - s) * Real.log (ρ x)

noncomputable def differenceLogRight {n : ℕ} (f ρ : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) : ℝ :=
  ∫ x, f x * f (x - s) * Real.log (ρ (x - s))

theorem differenceLogLeft_eq_crossDifferenceDensity {n : ℕ} (f ρ : (Fin n → ℝ) → ℝ) :
    differenceLogLeft f ρ = crossDifferenceDensity (fun x => f x * Real.log (ρ x)) f := by
  funext s
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem differenceLogRight_eq_crossDifferenceDensity {n : ℕ} (f ρ : (Fin n → ℝ) → ℝ) :
    differenceLogRight f ρ = crossDifferenceDensity f (fun x => f x * Real.log (ρ x)) := by
  funext s
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem power_logDifference_moments {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (differenceLogLeft (powerDensity m K ρ) ρ) volume ∧
      Integrable (differenceLogRight (powerDensity m K ρ) ρ) volume ∧
      (∫ s, differenceLogLeft (powerDensity m K ρ) ρ s) =
        (∫ x, powerDensity m K ρ x * Real.log (ρ x)) ∧
      (∫ s, differenceLogRight (powerDensity m K ρ) ρ s) =
        (∫ x, powerDensity m K ρ x * Real.log (ρ x)) := by
  have hf := isProbabilityDensity_powerDensity (m := m) hK hfin hpos hρ hc hC.le hb
  have hlog := integrable_powerDensity_mul_log (m := m) hK hfin hpos hρ hc hC hb
  rw [differenceLogLeft_eq_crossDifferenceDensity, differenceLogRight_eq_crossDifferenceDensity]
  refine ⟨integrable_crossDifferenceDensity hlog hf.2.2.1,
    integrable_crossDifferenceDensity hf.2.2.1 hlog, ?_, ?_⟩
  · rw [integral_crossDifferenceDensity hlog hf.2.2.1, hf.2.2.2, mul_one]
  · rw [integral_crossDifferenceDensity hf.2.2.1 hlog, hf.2.2.2, one_mul]

theorem fiber_difference_entropy_lower_bound {n m : ℕ} [NeZero m]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ) (hcont : ContinuousOn ρ K)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C) :
    differentialEntropy (differenceDensity (powerDensity m K ρ)) volume +
      differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
        (uniformDensity (simplex m 1))) volume +
      (m : ℝ) * (∫ x, powerDensity m K ρ x * Real.log (ρ x)) ≤
        differentialEntropy (fiberDifferenceDensity (m := m) K ρ) volume := by
  let f := powerDensity m K ρ
  let S := differenceDensity f
  let E := differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
    (uniformDensity (simplex m 1))) volume
  let A := differenceLogLeft f ρ
  let B := differenceLogRight f ρ
  have hf := isProbabilityDensity_powerDensity (m := m) hK.measurableSet hK.measure_ne_top hpos hρ hc hC.le
    (fun x _ => hb x)
  have hS := isProbabilityDensity_differenceDensity hf
  have hSE := integrable_negMulLog_powerDifferenceDensity (m := m) hK hpos hρ hc hC (fun x _ => hb x)
  obtain ⟨hA, hB, hAm, hBm⟩ := power_logDifference_moments (m := m) hK.measurableSet hK.measure_ne_top
    hpos hρ hc hC (fun x _ => hb x)
  have hJ := integrable_negMulLog_fiberDifferenceDensity (m := m) hK hpos hρ hcont hc hC.le
    (fun x _ => hb x)
  rw [Measure.volume_eq_prod] at hJ
  have hL : Integrable (fun s => Real.negMulLog (S s) + S s * E + (m : ℝ) / 2 * (A s + B s)) volume :=
    (hSE.add (hS.2.2.1.mul_const E)).add ((hA.add hB).const_mul _)
  have h := integral_mono hL hJ.integral_prod_left
    (fun s => fiber_row_entropy_lower_bound hK hpos hρ hc hC hb s)
  have he : (∫ s, Real.negMulLog (S s) + S s * E + (m : ℝ) / 2 * (A s + B s)) =
      differentialEntropy S volume + E + (m : ℝ) * (∫ x, f x * Real.log (ρ x)) := by
    rw [integral_add (f := fun s => Real.negMulLog (S s) + S s * E)
      (g := fun s => (m : ℝ) / 2 * (A s + B s))
      (hSE.add (hS.2.2.1.mul_const E)) ((hA.add hB).const_mul _),
      integral_add (f := fun s => Real.negMulLog (S s)) (g := fun s => S s * E)
        hSE (hS.2.2.1.mul_const E), integral_mul_const, integral_const_mul,
      integral_add (f := fun s => A s) (g := fun s => B s) hA hB, hS.2.2.2, hAm, hBm]
    dsimp only [differentialEntropy]
    ring
  rw [he] at h
  change differentialEntropy S volume + E + (m : ℝ) * (∫ x, f x * Real.log (ρ x)) ≤
    ∫ s, differentialEntropy (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) volume at h
  have hJE : differentialEntropy (fiberDifferenceDensity (m := m) K ρ) volume =
      ∫ s, differentialEntropy (fun t : Fin m → ℝ => fiberDifferenceDensity K ρ (s, t)) volume := by
    exact integral_prod _ hJ
  rw [← hJE] at h
  exact h

theorem global_power_density_entropy_increment_bound {n m : ℕ} [NeZero m] [NeZero (n + m)]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hcont : ContinuousOn ρ K) (hconc : ConcaveOn ℝ K ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x, ρ x ∈ Icc c C) :
    differentialEntropy (differenceDensity (powerDensity m K ρ)) volume -
      differentialEntropy (powerDensity m K ρ) volume ≤ F (n + m) - F m := by
  have hu := fiber_difference_entropy_upper_bound (m := m) hK hpos hρ hcont hconc hc hC
    (fun x _ => hb x)
  have hl := fiber_difference_entropy_lower_bound (m := m) hK hpos hρ hcont hc hC hb
  rw [differentialEntropy_uniformSimplexDifference_equal] at hl
  linarith

end EntropicRogersShephard
