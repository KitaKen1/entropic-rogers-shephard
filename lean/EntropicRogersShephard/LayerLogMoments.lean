import EntropicRogersShephard.LayerCoefficients

/-! Logarithmic layer moments by an elementary primitive and integer Beta moments. -/

open Real MeasureTheory Set Finset intervalIntegral
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def radiusLogPrimitive (m : ℕ) (r : ℝ) : ℝ :=
  r ^ m * (-Real.log r + 1 / (m : ℝ))

noncomputable def radiusLogKernel (m : ℕ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun u => (m : ℝ) * u ^ (m - 1) * (-Real.log u)) t

theorem intervalIntegrable_radiusLogKernel (m : ℕ) (r : ℝ) :
    IntervalIntegrable (radiusLogKernel m) volume 0 r := by
  have hi : IntervalIntegrable (fun t : ℝ => (m : ℝ) * t ^ (m - 1) * (-Real.log t))
      volume 0 r :=
    (intervalIntegrable_log'.neg : IntervalIntegrable (fun t : ℝ => -Real.log t) volume 0 r)
      |>.continuousOn_mul (by fun_prop)
  exact ⟨hi.1.indicator measurableSet_Ioc, hi.2.indicator measurableSet_Ioc⟩

theorem radiusLogKernel_nonneg (m : ℕ) (t : ℝ) : 0 ≤ radiusLogKernel m t := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [radiusLogKernel, Set.indicator_of_mem ht]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg ht.1.le _))
      (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2))
  · simp [radiusLogKernel, ht]

/-- The primitive is continuous at zero, so no parameter derivative is needed. -/
theorem integral_radiusLogKernel (m : ℕ) [NeZero m] {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ t in 0..r, radiusLogKernel m t) = radiusLogPrimitive m r := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : m - 1 + 1 = m := by omega
  have hc : Continuous (radiusLogPrimitive m) := by
    have hlog : Continuous (fun t : ℝ => t ^ m * Real.log t) := by
      simpa only [he] using continuous_pow_succ_mul_log (m - 1)
    convert hlog.neg.add ((continuous_pow m).div_const (m : ℝ)) using 1
    funext t
    dsimp [radiusLogPrimitive]
    ring
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) r) :
      HasDerivAt (radiusLogPrimitive m) ((m : ℝ) * t ^ (m - 1) * (-Real.log t)) t := by
    have h := (((hasDerivAt_id t).pow m).mul (Real.hasDerivAt_log ht.1.ne')).neg.add
      (((hasDerivAt_id t).pow m).div_const (m : ℝ))
    convert h using 1
    · funext u
      dsimp [radiusLogPrimitive]
      ring
    · simp only [id_eq, Pi.pow_apply, mul_one]
      change (m : ℝ) * t ^ (m - 1) * (-Real.log t) =
        -((m : ℝ) * t ^ (m - 1) * Real.log t + t ^ m * t⁻¹) +
          (m : ℝ) * t ^ (m - 1) / (m : ℝ)
      have hp : t ^ m = t ^ (m - 1) * t := by
        simpa only [he] using (pow_succ t (m - 1))
      rw [hp]
      field_simp [ht.1.ne', hmR]
      ring
  have hi : IntervalIntegrable (fun t : ℝ => (m : ℝ) * t ^ (m - 1) * (-Real.log t))
      volume 0 r :=
    (intervalIntegrable_log'.neg : IntervalIntegrable (fun t : ℝ => -Real.log t) volume 0 r)
      |>.continuousOn_mul (by fun_prop)
  calc
    (∫ t in 0..r, radiusLogKernel m t) =
        ∫ t in 0..r, (m : ℝ) * t ^ (m - 1) * (-Real.log t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hr
      intro t ht
      change (Ioc (0 : ℝ) 1).indicator _ t = _
      exact Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le.trans hr1⟩) _
    _ = radiusLogPrimitive m r - radiusLogPrimitive m 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr hc.continuousOn hd hi
    _ = radiusLogPrimitive m r := by simp [radiusLogPrimitive, zero_pow hm.ne']

/-- The logarithmic layer integral after the coefficients have been fixed. -/
theorem orthant_polynomial_log_moment (m : ℕ) [NeZero m] (s : ℝ) :
    (∫ t in 0..1,
      orthantVolumePolynomial m (1 + s) 1 t * ((m : ℝ) * t ^ (m - 1) * (-Real.log t))) =
        (volume (simplex m 1)).toReal *
          ∑ j ∈ range (m + 1), (m.choose j : ℝ) * s ^ j * (H (2 * m - j) - H (m - 1)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have he (t : ℝ) :
      orthantVolumePolynomial m (1 + s) 1 t * ((m : ℝ) * t ^ (m - 1) * (-Real.log t)) =
        ∑ j ∈ range (m + 1),
          ((orthantCoefficient m j * (m : ℝ)) * s ^ j) *
            (t ^ (m - 1) * (1 - t) ^ (m - j) * (-Real.log t)) := by
    rw [orthantVolumePolynomial_binomial, Finset.sum_mul]
    apply sum_congr rfl
    intro j _
    have hs : 1 + s - 1 = s := by ring
    rw [hs]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hidx : m - 1 + (m - j) + 1 = 2 * m - j := by omega
    rw [intervalIntegral.integral_const_mul]
    change ((orthantCoefficient m j * (m : ℝ)) * s ^ j) * betaLogMoment (m - 1) (m - j) = _
    rw [betaLogMoment_eq_harmonic, hidx]
    have hc := orthantCoefficient_beta m hjm
    calc
      _ = (orthantCoefficient m j * (m : ℝ) * integerBeta (m - 1) (m - j)) *
          (s ^ j * (H (2 * m - j) - H (m - 1))) := by ring
      _ = _ := by rw [hc]; ring
  · intro j _
    exact (intervalIntegrable_betaLogMoment _ _).const_mul _

theorem radiusLogPrimitive_nonneg (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ radiusLogPrimitive m r := by
  unfold radiusLogPrimitive
  exact mul_nonneg (pow_nonneg hr _) (add_nonneg
    (neg_nonneg.mpr (Real.log_nonpos hr hr1)) (by positivity))

/-- ENNReal layer cake for the actual logarithmic primitive, at the unit smaller scale. -/
theorem lintegral_overlapRadius_log_primitive (m : ℕ) [NeZero m] {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (radiusLogPrimitive m (overlapRadius (1 + s) 1 z))) =
      ENNReal.ofReal ((volume (simplex m 1)).toReal *
        ∑ j ∈ range (m + 1), (m.choose j : ℝ) * s ^ j * (H (2 * m - j) - H (m - 1))) := by
  have hmoment := overlapRadius_layercake_bounded m (1 + s) (by norm_num : (0 : ℝ) ≤ 1)
    (radiusLogKernel m) (fun r _ => intervalIntegrable_radiusLogKernel m r)
    (Filter.Eventually.of_forall (radiusLogKernel_nonneg m))
  simp_rw [integral_radiusLogKernel m (overlapRadius_nonneg _ _ _)
    (overlapRadius_le_right _ _ _ (by norm_num : (0 : ℝ) ≤ 1))] at hmoment
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc :
    Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc (0 : ℝ) 1)] at hmoment
  let f : ℝ → ℝ := fun t => orthantVolumePolynomial m (1 + s) 1 t *
    ((m : ℝ) * t ^ (m - 1) * (-Real.log t))
  have hi : IntervalIntegrable f volume 0 1 := by
    have hco : Continuous (fun t : ℝ => orthantVolumePolynomial m (1 + s) 1 t *
        ((m : ℝ) * t ^ (m - 1))) :=
      (continuous_orthantVolumePolynomial m (1 + s) 1).mul
        (continuous_const.mul (continuous_id.pow (m - 1)))
    have h := (intervalIntegrable_log'.neg :
        IntervalIntegrable (fun t : ℝ => -Real.log t) volume 0 1).continuousOn_mul
      hco.continuousOn
    convert h using 1
    funext t
    dsimp [f]
    ring
  have hnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ f t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact mul_nonneg (orthantVolumePolynomial_nonneg m (by linarith [ht.2]) ht.2.le)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg ht.1.le _))
        (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2.le)))
  have he : (∫⁻ t in Ioo (0 : ℝ) 1,
      volume {z : Fin m → ℝ | t ≤ overlapRadius (1 + s) 1 z} *
        ENNReal.ofReal (radiusLogKernel m t)) = ENNReal.ofReal (∫ t in 0..1, f t) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal (hi.1.mono_set Ioo_subset_Ioc_self) hnn]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only [f]
    rw [volume_overlap_superlevel_eq_ofReal_polynomial m ht.1 (by linarith [ht.2]) ht.2,
      radiusLogKernel, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      ENNReal.ofReal_mul (orthantVolumePolynomial_nonneg m (by linarith [ht.2]) ht.2.le)]
  rw [he] at hmoment
  simpa only [f, orthant_polynomial_log_moment] using hmoment

end EntropicRogersShephard
