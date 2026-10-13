import EntropicRogersShephard.ConcaveApproximation

/-! Normalize the concave powers and pass their actual entropy increment bound to the exponential. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem shifted_normalizedPowerApproximation_bound {n : ℕ} {M : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : IsCompact K) (hpos : volume K ≠ 0)
    (hm : Measurable V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    ∃ J : ℕ, ∀ j x, normalizedPowerApproximation M K V (j + J) x ∈
      Icc (0 : ℝ) (2 / powerMass 1 K (fun x => Real.exp (-V x))) := by
  have hZ := compact_exponential_mass_pos hK.measurableSet hK.measure_ne_top hpos hm hb
  obtain ⟨J, hJ⟩ := positive_mass_lower_after_shift hZ
    (concave_power_mass_tendsto hK.measurableSet hK.measure_ne_top hm hR hM hb)
  refine ⟨J, ?_⟩
  intro j x
  have hf := isProbabilityDensity_normalizedPowerApproximation (M := M) (j := j + J)
    hK.measurableSet hK.measure_ne_top hpos hm hR hM hb
  have hZj := concave_power_mass_pos (j := j + J) hK.measurableSet hK.measure_ne_top hpos hm hR hM hb
  have hs : ∀ y ∈ K, concavePowerSize M V (j + J) y ∈ Icc (0 : ℝ) 1 :=
    fun y hy => ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans (concavePowerSize_mem_Icc hR hM hb hy).1,
      (concavePowerSize_mem_Icc hR hM hb hy).2⟩
  refine ⟨hf.2.1 x, ?_⟩
  calc
    normalizedPowerApproximation M K V (j + J) x ≤
        1 / powerMass (j + J + M) K (concavePowerSize M V (j + J)) := by
      change powerDensity (j + J + M) K (concavePowerSize M V (j + J)) x ≤ _
      simpa only [one_pow] using powerDensity_le hZj (by norm_num : (0 : ℝ) ≤ 1) hs x
    _ ≤ 1 / (powerMass 1 K (fun x => Real.exp (-V x)) / 2) :=
      one_div_le_one_div_of_le (by linarith) (hJ j)
    _ = 2 / powerMass 1 K (fun x => Real.exp (-V x)) := by ring

theorem compact_exponential_entropy_increment_bound {n : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : IsCompact K) (hpos : volume K ≠ 0)
    (hm : Measurable V) (hc : ContinuousOn V K) (hV : ConvexOn ℝ K V) (hR : 0 ≤ R)
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    differentialEntropy (differenceDensity (compactExponentialDensity K V)) volume -
      differentialEntropy (compactExponentialDensity K V) volume ≤ (n : ℝ) * Real.log 2 := by
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (2 * R)
  obtain ⟨J, hB⟩ := shifted_normalizedPowerApproximation_bound hK hpos hm hR hM hb
  let f := fun j => normalizedPowerApproximation M K V (j + J)
  have hZ := compact_exponential_mass_pos hK.measurableSet hK.measure_ne_top hpos hm hb
  have hprob : ∀ j, IsProbabilityDensity n (f j) := fun j =>
    isProbabilityDensity_normalizedPowerApproximation hK.measurableSet hK.measure_ne_top hpos hm hR hM hb
  have hpoint : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (compactExponentialDensity K V x)) := by
    intro x
    exact (normalizedPowerApproximation_tendsto hK.measurableSet hK.measure_ne_top hpos hm hR hM hb x).comp
      (tendsto_add_atTop_nat J)
  have hsupp : ∀ j x, x ∉ K → f j x = 0 := fun _ _ hx => powerDensity_eq_zero_of_not_mem hx
  have hinput := entropy_tendsto_of_bounded_support (μ := volume) hK.measurableSet hK.measure_ne_top
    (fun j => (hprob j).1) hB hsupp hpoint
  have hdiff := difference_entropy_tendsto_of_compact_support hK (by positivity :
    0 ≤ 2 / powerMass 1 K (fun x => Real.exp (-V x))) hprob hB hsupp hpoint
  have hF : Tendsto (fun j : ℕ => F (n + (j + J + M)) - F (j + J + M)) atTop
      (𝓝 ((n : ℝ) * Real.log 2)) := by
    simpa only [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (tendsto_F_shift_sub n).comp (tendsto_add_atTop_nat (J + M))
  exact le_of_tendsto_of_tendsto' (hdiff.sub hinput) hF (fun j =>
    normalizedPowerApproximation_entropy_increment_bound (j := j + J) hK hpos hm hc hV hR hM hb)

theorem compact_exponential_entropy_finite_and_bound {n : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : IsCompact K) (hpos : volume K ≠ 0)
    (hm : Measurable V) (hc : ContinuousOn V K) (hV : ConvexOn ℝ K V) (hR : 0 ≤ R)
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    Integrable (fun x => Real.negMulLog (compactExponentialDensity K V x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity (compactExponentialDensity K V) s)) volume ∧
      differentialEntropy (differenceDensity (compactExponentialDensity K V)) volume -
        differentialEntropy (compactExponentialDensity K V) volume ≤ (n : ℝ) * Real.log 2 := by
  refine ⟨?_, ?_, compact_exponential_entropy_increment_bound hK hpos hm hc hV hR hb⟩
  · exact integrable_negMulLog_powerDensity hK.measurableSet hK.measure_ne_top hpos hm.neg.exp
      (Real.exp_pos _) (by norm_num) (fun _ hx => exponential_size_bounds hb hx)
  · exact integrable_negMulLog_powerDifferenceDensity hK hpos hm.neg.exp
      (Real.exp_pos _) (by norm_num) (fun _ hx => exponential_size_bounds hb hx)

end EntropicRogersShephard
