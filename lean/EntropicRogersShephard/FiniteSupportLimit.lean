import EntropicRogersShephard.PowerDensity

/-! Mass convergence on a bounded finite support and a positive lower mass after a finite shift. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem integral_tendsto_of_bounded_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {K : Set α} {f : ℕ → α → ℝ} {g : α → ℝ} {C : ℝ}
    (hK : MeasurableSet K) (hfin : μ K ≠ ∞) (hm : ∀ j, Measurable (f j))
    (hb : ∀ j x, f j x ∈ Icc (0 : ℝ) C) (hsupp : ∀ j x, x ∉ K → f j x = 0)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto (fun j => ∫ x, f j x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hi : Integrable (K.indicator (fun _ : α => C)) μ := by
    rw [integrable_indicator_iff hK]
    exact integrableOn_const hfin
  apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => C))
    (fun j => (hm j).aestronglyMeasurable) hi
  · intro j
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hb j x).1]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact (hb j x).2
    · simp [hx, hsupp j x hx]
  · exact Filter.Eventually.of_forall hlim

theorem positive_mass_lower_after_shift {Z : ℕ → ℝ} {z : ℝ} (hz : 0 < z)
    (hlim : Tendsto Z atTop (𝓝 z)) : ∃ J : ℕ, ∀ j, z / 2 ≤ Z (j + J) := by
  have hh : z / 2 < z := by linarith
  have he := hlim.eventually (eventually_gt_nhds hh)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 he
  exact ⟨J, fun j => (hJ (j + J) (by omega)).le⟩

theorem powerDensity_one_const_mul {n : ℕ} {K : Set (Fin n → ℝ)}
    (ρ : (Fin n → ℝ) → ℝ) {a : ℝ} (ha : a ≠ 0) :
    powerDensity 1 K (fun x => a * ρ x) = powerDensity 1 K ρ := by
  have hw : powerWeight 1 K (fun x => a * ρ x) = (fun x => a * powerWeight 1 K ρ x) := by
    funext x
    by_cases hx : x ∈ K <;> simp [powerWeight, hx]
  have hZ : powerMass 1 K (fun x => a * ρ x) = a * powerMass 1 K ρ := by
    change (∫ x, powerWeight 1 K (fun x => a * ρ x) x) = a * powerMass 1 K ρ
    rw [hw, integral_const_mul]
    rfl
  funext x
  change powerWeight 1 K (fun x => a * ρ x) x / powerMass 1 K (fun x => a * ρ x) =
    powerWeight 1 K ρ x / powerMass 1 K ρ
  rw [congrFun hw x, hZ, mul_div_mul_left _ _ ha]

end EntropicRogersShephard
