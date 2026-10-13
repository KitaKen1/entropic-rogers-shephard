import EntropicRogersShephard.FiberCancellation

/-! Extend the fiber size by one outside its support, preserving the power density. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def positiveFiberExtension {n : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ := by
  classical
  exact K.piecewise ρ (fun _ => 1)

theorem positiveFiberExtension_eq_on {n : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : EqOn (positiveFiberExtension K ρ) ρ K := by
  classical
  intro x hx
  simp [positiveFiberExtension, hx]

theorem measurable_positiveFiberExtension {n : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    Measurable (positiveFiberExtension K ρ) := by
  classical
  exact hρ.piecewise hK measurable_const

theorem positiveFiberExtension_bounds {n : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hb : ∀ x ∈ K, ρ x ∈ Icc c C) (x : Fin n → ℝ) :
    positiveFiberExtension K ρ x ∈ Icc (min c 1) (max C 1) := by
  classical
  by_cases hx : x ∈ K
  · rw [positiveFiberExtension_eq_on K ρ hx]
    exact ⟨(min_le_left _ _).trans (hb x hx).1, (hb x hx).2.trans (le_max_left _ _)⟩
  · have he : positiveFiberExtension K ρ x = 1 := by simp [positiveFiberExtension, hx]
    rw [he]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem powerWeight_congr_on_support {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ σ : (Fin n → ℝ) → ℝ} (he : EqOn ρ σ K) : powerWeight m K ρ = powerWeight m K σ := by
  funext x
  by_cases hx : x ∈ K
  · simp only [powerWeight, Set.indicator_of_mem hx, he hx]
  · simp [powerWeight, hx]

theorem powerDensity_congr_on_support {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ σ : (Fin n → ℝ) → ℝ} (he : EqOn ρ σ K) : powerDensity m K ρ = powerDensity m K σ := by
  have hw := powerWeight_congr_on_support (m := m) he
  have hZ : powerMass m K ρ = powerMass m K σ := by
    change (∫ x, powerWeight m K ρ x) = ∫ x, powerWeight m K σ x
    rw [hw]
  funext x
  change powerWeight m K ρ x / powerMass m K ρ = powerWeight m K σ x / powerMass m K σ
  rw [hw, hZ]

theorem power_density_entropy_increment_bound {n m : ℕ} [NeZero m] [NeZero (n + m)]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hcont : ContinuousOn ρ K) (hconc : ConcaveOn ℝ K ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    differentialEntropy (differenceDensity (powerDensity m K ρ)) volume -
      differentialEntropy (powerDensity m K ρ) volume ≤ F (n + m) - F m := by
  let σ := positiveFiberExtension K ρ
  have he : EqOn σ ρ K := positiveFiberExtension_eq_on K ρ
  have hσ : Measurable σ := measurable_positiveFiberExtension hK.measurableSet hρ
  have hσcont : ContinuousOn σ K := hcont.congr he
  have hσconc : ConcaveOn ℝ K σ := by
    refine ⟨hconc.1, ?_⟩
    intro x hx y hy a b ha hb' hab
    rw [he hx, he hy, he (hconc.1 hx hy ha hb' hab)]
    exact hconc.2 hx hy ha hb' hab
  have h := global_power_density_entropy_increment_bound (m := m) hK hpos hσ hσcont hσconc
    (lt_min hc (by norm_num : (0 : ℝ) < 1))
    ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_right C 1))
    (positiveFiberExtension_bounds hb)
  rw [powerDensity_congr_on_support he] at h
  exact h

end EntropicRogersShephard
