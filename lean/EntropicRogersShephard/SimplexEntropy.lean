import EntropicRogersShephard.LayerLogMoments

/-! The logarithmic moment is the entropy of the actual simplex difference density. -/

open MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem radiusLogPrimitive_eq_density_entropy (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (z : Fin m → ℝ) :
    radiusLogPrimitive m (overlapRadius a b z) =
      (a ^ m * b ^ m * (volume (simplex m 1)).toReal / (m : ℝ)) *
        (Real.negMulLog (crossDifferenceDensity (uniformDensity (simplex m a))
            (uniformDensity (simplex m b)) z) +
          (1 - Real.log (a ^ m * b ^ m * (volume (simplex m 1)).toReal)) *
            crossDifferenceDensity (uniformDensity (simplex m a))
              (uniformDensity (simplex m b)) z) := by
  let D := a ^ m * b ^ m * (volume (simplex m 1)).toReal
  let d := crossDifferenceDensity (uniformDensity (simplex m a))
    (uniformDensity (simplex m b))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hv : (volume (simplex m 1)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
  have he : overlapRadius a b z ^ m = D * d z := by
    dsimp [D, d]
    rw [crossDifferenceDensity_uniformSimplex m ha hb]
    field_simp [ha.ne', hb.ne', hv]
  have hp : radiusLogPrimitive m (overlapRadius a b z) =
      (Real.negMulLog (overlapRadius a b z ^ m) + overlapRadius a b z ^ m) / (m : ℝ) := by
    simp only [radiusLogPrimitive, Real.negMulLog, Real.log_pow]
    field_simp [hmR]
    <;> ring
  rw [hp, he, Real.negMulLog_mul]
  change (d z * Real.negMulLog D + D * Real.negMulLog (d z) + D * d z) / (m : ℝ) = _
  simp only [Real.negMulLog]
  dsimp only [D, d]
  ring

theorem integrable_radiusLogPrimitive_overlap (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun z : Fin m → ℝ => radiusLogPrimitive m (overlapRadius a b z)) volume := by
  let d := crossDifferenceDensity (uniformDensity (simplex m a))
    (uniformDensity (simplex m b))
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha) (isProbabilityDensity_uniformSimplex m hb)
  have hh := integrable_negMulLog_uniformSimplexDifference m ha hb
  have hi := (hh.add (hd.2.2.1.const_mul
    (1 - Real.log (a ^ m * b ^ m * (volume (simplex m 1)).toReal)))).const_mul
      (a ^ m * b ^ m * (volume (simplex m 1)).toReal / (m : ℝ))
  exact hi.congr (Filter.Eventually.of_forall fun z =>
    (radiusLogPrimitive_eq_density_entropy m ha hb z).symm)

theorem integral_radiusLogPrimitive_eq_entropy (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    (∫ z : Fin m → ℝ, radiusLogPrimitive m (overlapRadius a b z)) =
      (a ^ m * b ^ m * (volume (simplex m 1)).toReal / (m : ℝ)) *
        (differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
          (uniformDensity (simplex m b))) volume +
            1 - Real.log (a ^ m * b ^ m * (volume (simplex m 1)).toReal)) := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha) (isProbabilityDensity_uniformSimplex m hb)
  simp_rw [radiusLogPrimitive_eq_density_entropy m ha hb]
  rw [integral_const_mul, integral_add
    (integrable_negMulLog_uniformSimplexDifference m ha hb) (hd.2.2.1.const_mul _),
    integral_const_mul, hd.2.2.2]
  unfold differentialEntropy
  ring

theorem integral_overlapRadius_log_primitive (m : ℕ) [NeZero m] {s : ℝ} (hs : 0 ≤ s) :
    (∫ z : Fin m → ℝ, radiusLogPrimitive m (overlapRadius (1 + s) 1 z)) =
      (volume (simplex m 1)).toReal *
        ∑ j ∈ range (m + 1), (m.choose j : ℝ) * s ^ j * (H (2 * m - j) - H (m - 1)) := by
  have hi := integrable_radiusLogPrimitive_overlap m
    (by linarith : 0 < 1 + s) (by norm_num : (0 : ℝ) < 1)
  have hnn : ∀ z : Fin m → ℝ, 0 ≤ radiusLogPrimitive m (overlapRadius (1 + s) 1 z) :=
    fun z => radiusLogPrimitive_nonneg m (overlapRadius_nonneg _ _ _)
      (overlapRadius_le_right _ _ _ (by norm_num : (0 : ℝ) ≤ 1))
  have hright : 0 ≤ (volume (simplex m 1)).toReal *
      ∑ j ∈ range (m + 1), (m.choose j : ℝ) * s ^ j * (H (2 * m - j) - H (m - 1)) := by
    rw [← orthant_polynomial_log_moment m s,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact mul_nonneg (orthantVolumePolynomial_nonneg m (by linarith [ht.2]) ht.2)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg ht.1.le _))
        (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2)))
  have h := lintegral_overlapRadius_log_primitive m hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)] at h
  have he := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hnn), ENNReal.toReal_ofReal hright] using he

theorem binomialWeight_unit_ratio (m : ℕ) {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : j ≤ m) :
    binomialWeight m (1 - 1 / a) j = (m.choose j : ℝ) * (a - 1) ^ j / a ^ m := by
  have hq : 1 - 1 / a = (a - 1) / a := by field_simp [ha.ne'] <;> ring
  unfold binomialWeight
  rw [hq]
  have hq' : 1 - (a - 1) / a = 1 / a := by field_simp [ha.ne'] <;> ring
  rw [hq', div_pow, div_pow, one_pow]
  calc
    _ = (m.choose j : ℝ) * (a - 1) ^ j / (a ^ j * a ^ (m - j)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj]

/-- Exact entropy of the difference of two uniform simplices, when the smaller scale is one. -/
theorem differentialEntropy_uniformSimplexDifference_unit (m : ℕ) [NeZero m]
    {a : ℝ} (ha : 1 ≤ a) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m 1))) volume =
        (m : ℝ) * Real.log a + Real.log (volume (simplex m 1)).toReal +
          (m : ℝ) * ((∑ j ∈ range (m + 1),
            binomialWeight m (1 - 1 / a) j * H (2 * m - j)) - H m) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ha
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let V := (volume (simplex m 1)).toReal
  let D := a ^ m * V
  let d := crossDifferenceDensity (uniformDensity (simplex m a))
    (uniformDensity (simplex m 1))
  have hv : 0 < V := ENNReal.toReal_pos (volume_unit_simplex_pos m).ne'
    (volume_simplex_ne_top m 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hI := integral_overlapRadius_log_primitive m (sub_nonneg.mpr ha)
  have haid : 1 + (a - 1) = a := by ring
  rw [haid, integral_radiusLogPrimitive_eq_entropy m ha0 (by norm_num : (0 : ℝ) < 1)] at hI
  simp only [one_pow, mul_one] at hI
  have hw : (∑ j ∈ range (m + 1),
      (m.choose j : ℝ) * (a - 1) ^ j * (H (2 * m - j) - H (m - 1))) =
        a ^ m * ((∑ j ∈ range (m + 1),
          binomialWeight m (1 - 1 / a) j * H (2 * m - j)) - H (m - 1)) := by
    calc
      _ = a ^ m * ∑ j ∈ range (m + 1),
          binomialWeight m (1 - 1 / a) j * (H (2 * m - j) - H (m - 1)) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [binomialWeight_unit_ratio m ha0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        field_simp [ha0.ne']
        <;> ring
      _ = _ := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_binomialWeight, one_mul]
        <;> ring
  have he : m - 1 + 1 = m := by omega
  have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast he
  have hH : H m = H (m - 1) + 1 / (m : ℝ) := by
    have h := H_succ (m - 1)
    rwa [he, hc] at h
  rw [hw] at hI
  have hlog : Real.log D = (m : ℝ) * Real.log a + Real.log V := by
    dsimp [D]
    rw [Real.log_mul (pow_ne_zero _ ha0.ne') hv.ne', Real.log_pow]
  change differentialEntropy d volume = _
  change D / (m : ℝ) * (differentialEntropy d volume + 1 - Real.log D) =
    V * (a ^ m * ((∑ j ∈ range (m + 1),
      binomialWeight m (1 - 1 / a) j * H (2 * m - j)) - H (m - 1))) at hI
  have hn := congrArg (fun r : ℝ => (m : ℝ) / D * r) hI
  have hcancel : (m : ℝ) / D * (D / (m : ℝ) *
      (differentialEntropy d volume + 1 - Real.log D)) =
        differentialEntropy d volume + 1 - Real.log D := by field_simp [hmR, hD.ne']
  have hrhs : (m : ℝ) / D * (V * (a ^ m * ((∑ j ∈ range (m + 1),
      binomialWeight m (1 - 1 / a) j * H (2 * m - j)) - H (m - 1)))) =
        (m : ℝ) * ((∑ j ∈ range (m + 1),
          binomialWeight m (1 - 1 / a) j * H (2 * m - j)) - H (m - 1)) := by
    dsimp [D]
    field_simp [ha0.ne', hv.ne']
    <;> ring
  rw [hcancel, hrhs] at hn
  rw [← hlog, hH]
  field_simp [hmR] at hn ⊢
  linarith

end EntropicRogersShephard
