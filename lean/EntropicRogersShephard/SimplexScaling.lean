import EntropicRogersShephard.SimplexEntropy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Scale transport and the entropy comparison for the actual simplex difference. -/

open Real MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem positiveMass_smul {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (z : Fin m → ℝ) :
    positiveMass (c • z) = c * positiveMass z := by
  unfold positiveMass
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, mul_max_of_nonneg _ _ hc, mul_zero]

theorem negativeMass_smul {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (z : Fin m → ℝ) :
    negativeMass (c • z) = c * negativeMass z := by
  unfold negativeMass
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_neg,
    mul_max_of_nonneg _ _ hc, mul_zero]

theorem overlapRadius_smul {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) (z : Fin m → ℝ) :
    overlapRadius (c * a) (c * b) (c • z) = c * overlapRadius a b z := by
  simp only [overlapRadius, rawRadius, positiveMass_smul hc, negativeMass_smul hc,
    ← mul_sub, ← mul_min_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc, mul_zero]

theorem crossDifferenceDensity_uniformSimplex_scaling (m : ℕ) [NeZero m]
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (z : Fin m → ℝ) :
    crossDifferenceDensity (uniformDensity (simplex m (c * a)))
      (uniformDensity (simplex m (c * b))) (c • z) =
        crossDifferenceDensity (uniformDensity (simplex m a))
          (uniformDensity (simplex m b)) z / c ^ m := by
  rw [crossDifferenceDensity_uniformSimplex m (mul_pos hc ha) (mul_pos hc hb),
    crossDifferenceDensity_uniformSimplex m ha hb, overlapRadius_smul hc.le]
  simp only [mul_pow]
  have hv : (volume (simplex m 1)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
  field_simp [ha.ne', hb.ne', hc.ne', hv]
  <;> ring

/-- Entropy transport follows directly from Haar scaling and the multiplication
identity for `negMulLog`; no random-variable change-of-law machinery is needed. -/
theorem differentialEntropy_scaling {m : ℕ} {f g : (Fin m → ℝ) → ℝ}
    {c : ℝ} (hc : 0 < c) (hg : Integrable g volume) (hgmass : (∫ z, g z) = 1)
    (hgent : Integrable (fun z => Real.negMulLog (g z)) volume)
    (hscale : ∀ z, f (c • z) = g z / c ^ m) :
    differentialEntropy f volume = differentialEntropy g volume + (m : ℝ) * Real.log c := by
  let C := (c ^ m)⁻¹
  have hC : C ≠ 0 := inv_ne_zero (pow_ne_zero _ hc.ne')
  have ht : (∫ z : Fin m → ℝ, Real.negMulLog (f (c • z))) = C * differentialEntropy f volume := by
    simpa only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul, differentialEntropy] using
      Measure.integral_comp_smul_of_nonneg volume (fun z => Real.negMulLog (f z)) c
        (hR := hc.le)
  have hp (z : Fin m → ℝ) : Real.negMulLog (f (c • z)) =
      C * Real.negMulLog (g z) + Real.negMulLog C * g z := by
    rw [hscale, div_eq_mul_inv, Real.negMulLog_mul]
    dsimp [C]
    ring
  apply (mul_left_cancel₀ hC)
  calc
    C * differentialEntropy f volume = ∫ z : Fin m → ℝ, Real.negMulLog (f (c • z)) := ht.symm
    _ = C * differentialEntropy g volume + Real.negMulLog C := by
      simp_rw [hp]
      rw [integral_add (hgent.const_mul C) (hg.const_mul _), integral_const_mul,
        integral_const_mul, hgmass, mul_one]
      rfl
    _ = C * (differentialEntropy g volume + (m : ℝ) * Real.log c) := by
      simp only [Real.negMulLog, C, Real.log_inv, Real.log_pow]
      ring

theorem differentialEntropy_uniformSimplexDifference_scaling (m : ℕ) [NeZero m]
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m (c * a)))
      (uniformDensity (simplex m (c * b)))) volume =
        differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
          (uniformDensity (simplex m b))) volume + (m : ℝ) * Real.log c := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha) (isProbabilityDensity_uniformSimplex m hb)
  exact differentialEntropy_scaling hc hd.2.2.1 hd.2.2.2
    (integrable_negMulLog_uniformSimplexDifference m ha hb)
    (crossDifferenceDensity_uniformSimplex_scaling m ha hb hc)

/-- Exact harmonic entropy formula at all ordered positive scales. -/
theorem differentialEntropy_uniformSimplexDifference (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b))) volume =
        (m : ℝ) * Real.log a + Real.log (volume (simplex m 1)).toReal +
          (m : ℝ) * ((∑ j ∈ range (m + 1),
            binomialWeight m (1 - b / a) j * H (2 * m - j)) - H m) := by
  have hA : 1 ≤ a / b := (le_div_iff₀ hb).mpr (by simpa using hba)
  have hscale : b * (a / b) = a := by field_simp [hb.ne']
  have hq : 1 - 1 / (a / b) = 1 - b / a := by field_simp [ha.ne', hb.ne'] <;> ring
  calc
    _ = differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m (a / b)))
        (uniformDensity (simplex m 1))) volume + (m : ℝ) * Real.log b := by
      simpa only [hscale, mul_one] using differentialEntropy_uniformSimplexDifference_scaling m
        (div_pos ha hb) (by norm_num : (0 : ℝ) < 1) hb
    _ = _ := by
      rw [differentialEntropy_uniformSimplexDifference_unit m hA, hq,
        Real.log_div ha.ne' hb.ne']
      ring

theorem sum_binomialWeight_zero (m : ℕ) (φ : ℕ → ℝ) :
    (∑ j ∈ range (m + 1), binomialWeight m 0 j * φ j) = φ 0 := by
  rw [Finset.sum_eq_single 0]
  · simp [binomialWeight]
  · intro j _ hj
    simp [binomialWeight, zero_pow hj]
  · intro h
    simp at h

theorem differentialEntropy_uniformSimplexDifference_equal (m : ℕ) [NeZero m] :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
      (uniformDensity (simplex m 1))) volume = Real.log (volume (simplex m 1)).toReal + F m := by
  rw [differentialEntropy_uniformSimplexDifference_unit m (le_refl (1 : ℝ))]
  simp only [Real.log_one, mul_zero, zero_add, div_one, sub_self, sum_binomialWeight_zero,
    Nat.sub_zero, F]

/-- The harmonic comparison now applies to the actual entropies. -/
theorem simplex_difference_entropy_scale_bound (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
        (uniformDensity (simplex m 1))) volume + (m : ℝ) / 2 * (Real.log a + Real.log b) ≤
      differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
        (uniformDensity (simplex m b))) volume := by
  rw [differentialEntropy_uniformSimplexDifference_equal,
    differentialEntropy_uniformSimplexDifference m ha hb hba]
  have h := harmonic_average_scale_bound m (Nat.pos_of_ne_zero (NeZero.ne m)) a b ha hb hba
  unfold F
  linarith

theorem simplex_difference_entropy_scale_strict (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
        (uniformDensity (simplex m 1))) volume + (m : ℝ) / 2 * (Real.log a + Real.log b) <
      differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
        (uniformDensity (simplex m b))) volume := by
  rw [differentialEntropy_uniformSimplexDifference_equal,
    differentialEntropy_uniformSimplexDifference m ha hb hba.le]
  have h := harmonic_average_scale_strict m (Nat.pos_of_ne_zero (NeZero.ne m)) a b ha hb hba
  unfold F
  linarith

theorem overlapRadius_swap_neg {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) :
    overlapRadius a b (-z) = overlapRadius b a z := by
  simp only [overlapRadius, rawRadius, positiveMass, negativeMass, Pi.neg_apply, neg_neg]
  rw [min_comm]

theorem crossDifferenceDensity_uniformSimplex_swap_neg (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : Fin m → ℝ) :
    crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b)) (-z) =
        crossDifferenceDensity (uniformDensity (simplex m b))
          (uniformDensity (simplex m a)) z := by
  rw [crossDifferenceDensity_uniformSimplex m ha hb,
    crossDifferenceDensity_uniformSimplex m hb ha, overlapRadius_swap_neg]
  congr 1
  ring

theorem differentialEntropy_uniformSimplexDifference_swap (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b))) volume =
        differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m b))
          (uniformDensity (simplex m a))) volume := by
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin m → ℝ))).integral_comp
    (Homeomorph.neg (Fin m → ℝ)).measurableEmbedding
    (fun z => Real.negMulLog (crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b)) z))
  simp_rw [crossDifferenceDensity_uniformSimplex_swap_neg m ha hb] at h
  exact h.symm

/-- The comparison holds for every positive pair, without an ordering hypothesis. -/
theorem simplex_difference_entropy_scale_bound_all (m : ℕ) [NeZero m]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m 1))
        (uniformDensity (simplex m 1))) volume + (m : ℝ) / 2 * (Real.log a + Real.log b) ≤
      differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
        (uniformDensity (simplex m b))) volume := by
  rcases le_total b a with hba | hab
  · exact simplex_difference_entropy_scale_bound m ha hb hba
  · rw [differentialEntropy_uniformSimplexDifference_swap m ha hb, add_comm (Real.log a)]
    exact simplex_difference_entropy_scale_bound m hb ha hab

end EntropicRogersShephard
