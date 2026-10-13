import EntropicRogersShephard.LayerNormalization

/-! Recover the layer coefficients from normalization, keeping block volumes symbolic. -/

open MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

/-- A binomial expansion with a common ambient degree. Out-of-range terms vanish. -/
theorem add_pow_mul_pow_common_degree {k l m : ℕ} (hkl : k + l = m) (s u : ℝ) :
    (s + u) ^ k * u ^ l =
      ∑ j ∈ range (m + 1), (k.choose j : ℝ) * s ^ j * u ^ (m - j) := by
  rw [add_pow, Finset.sum_mul]
  have hk : k ≤ m := by omega
  calc
    (∑ j ∈ range (k + 1), (s ^ j * u ^ (k - j) * (k.choose j : ℝ)) * u ^ l) =
        ∑ j ∈ range (k + 1), (k.choose j : ℝ) * s ^ j * u ^ (m - j) := by
      apply sum_congr rfl
      intro j hj
      have hpow : k - j + l = m - j := by have := mem_range.mp hj; omega
      rw [← hpow, pow_add]
      ring
    _ = ∑ j ∈ range (m + 1), (k.choose j : ℝ) * s ^ j * u ^ (m - j) := by
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      have hjk : k < j := by simp only [Finset.mem_range] at hj; omega
      simp [Nat.choose_eq_zero_of_lt hjk]

noncomputable def orthantCoefficient (m j : ℕ) : ℝ :=
  ∑ s : Finset (Fin m),
    ((volume (simplexOn {i : Fin m // i ∈ s} 1)).toReal *
      (volume (simplexOn {i : Fin m // i ∉ s} 1)).toReal) *
      (Fintype.card {i : Fin m // i ∈ s}).choose j

theorem orthantCoefficient_nonneg (m j : ℕ) : 0 ≤ orthantCoefficient m j := by
  apply sum_nonneg
  intro s _
  positivity

/-- The same coefficients work for every pair of scales. -/
theorem orthantVolumePolynomial_binomial (m : ℕ) (a b t : ℝ) :
    orthantVolumePolynomial m a b t =
      ∑ j ∈ range (m + 1), orthantCoefficient m j * (a - b) ^ j * (b - t) ^ (m - j) := by
  unfold orthantVolumePolynomial orthantCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  let k := Fintype.card {i : Fin m // i ∈ s}
  let l := Fintype.card {i : Fin m // i ∉ s}
  have hk : k ≤ m := by
    simpa [k] using Fintype.card_subtype_le (fun i : Fin m => i ∈ s)
  have hkl : k + l = m := by
    dsimp [k, l]
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    exact Nat.add_sub_of_le hk
  have hbin := add_pow_mul_pow_common_degree hkl (a - b) (b - t)
  have hab : a - b + (b - t) = a - t := by ring
  rw [hab] at hbin
  dsimp [k, l] at hbin
  calc
    _ = ((volume (simplexOn {i : Fin m // i ∈ s} 1)).toReal *
          (volume (simplexOn {i : Fin m // i ∉ s} 1)).toReal) *
          ((a - t) ^ Fintype.card {i : Fin m // i ∈ s} *
            (b - t) ^ Fintype.card {i : Fin m // i ∉ s}) := by ring
    _ = _ := by
      rw [hbin, Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- Integrating the expansion gives an actual polynomial identity. -/
theorem orthantCoefficient_moment (m : ℕ) [NeZero m] (s : ℝ) :
    (∫ t in 0..1, orthantVolumePolynomial m (1 + s) 1 t * ((m : ℝ) * t ^ (m - 1))) =
      ∑ j ∈ range (m + 1),
        (orthantCoefficient m j * (m : ℝ) * integerBeta (m - 1) (m - j)) * s ^ j := by
  have he (t : ℝ) :
      orthantVolumePolynomial m (1 + s) 1 t * ((m : ℝ) * t ^ (m - 1)) =
        ∑ j ∈ range (m + 1),
          ((orthantCoefficient m j * (m : ℝ)) * s ^ j) *
            (t ^ (m - 1) * (1 - t) ^ (m - j)) := by
    rw [orthantVolumePolynomial_binomial, Finset.sum_mul]
    apply sum_congr rfl
    intro j _
    have hs : 1 + s - 1 = s := by ring
    rw [hs]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
    change ((orthantCoefficient m j * (m : ℝ)) * s ^ j) * betaMoment (m - 1) (m - j) = _
    rw [betaMoment_eq_integerBeta]
    ring
  · intro j _
    exact (intervalIntegrable_betaMoment _ _).const_mul _

theorem orthantCoefficient_polynomial_normalization (m : ℕ) [NeZero m]
    {s : ℝ} (hs : 0 ≤ s) :
    (∑ j ∈ range (m + 1),
      (orthantCoefficient m j * (m : ℝ) * integerBeta (m - 1) (m - j)) * s ^ j) =
        (1 + s) ^ m * (volume (simplex m 1)).toReal := by
  rw [← orthantCoefficient_moment]
  simpa only [one_pow, mul_one] using orthant_polynomial_moment_normalization m
    (by linarith : 0 < 1 + s) (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ 1 + s)

/-- Normalization fixes every Beta-weighted coefficient, without a factorial volume formula. -/
theorem orthantCoefficient_beta (m : ℕ) [NeZero m] {j : ℕ} (hj : j ≤ m) :
    orthantCoefficient m j * (m : ℝ) * integerBeta (m - 1) (m - j) =
      (m.choose j : ℝ) * (volume (simplex m 1)).toReal := by
  let V := (volume (simplex m 1)).toReal
  have hv : V ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
  have h (s : ℝ) (hs : 0 ≤ s) :
      (∑ j ∈ range (m + 1),
        ((orthantCoefficient m j * (m : ℝ) * integerBeta (m - 1) (m - j)) / V) * s ^ j) =
          (1 + s) ^ m := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, orthantCoefficient_polynomial_normalization m hs]
    dsimp [V]
    exact mul_div_cancel_right₀ _ hv
  exact (div_eq_iff hv).mp (coefficients_eq_choose_of_normalization m _ h hj)

end EntropicRogersShephard
