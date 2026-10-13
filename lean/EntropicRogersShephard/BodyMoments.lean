import EntropicRogersShephard.BodyLayers

/-! Ordinary real layer-cake moments and their connection to the body entropy. -/

open Real MeasureTheory Set
open scoped ENNReal

namespace EntropicRogersShephard

theorem logPrimitive_eq_scaled_entropy (n : ℕ) [NeZero n] (r D v : ℝ)
    (hpow : r ^ n = D * v) :
    radiusLogPrimitive n r = (D / (n : ℝ)) * (Real.negMulLog v + (1 - Real.log D) * v) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hp : radiusLogPrimitive n r = (Real.negMulLog (r ^ n) + r ^ n) / (n : ℝ) := by
    simp only [radiusLogPrimitive, Real.negMulLog, Real.log_pow]
    field_simp [hn]
  rw [hp, hpow, Real.negMulLog_mul]
  simp only [Real.negMulLog]
  ring

theorem integrable_bodyRoot_power {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    Integrable (fun z => bodyOverlapRoot B z ^ n) volume := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
  exact (hd.2.2.1.const_mul (volume B).toReal).congr
    (Filter.Eventually.of_forall fun z => (bodyOverlapRoot_pow_eq_density hB hpos z).symm)

theorem integral_bodyRoot_power {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    (∫ z : Fin n → ℝ, bodyOverlapRoot B z ^ n) = (volume B).toReal := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
  simp_rw [bodyOverlapRoot_pow_eq_density hB hpos]
  rw [integral_const_mul, hd.2.2.2, mul_one]

theorem integrable_bodyRoot_logPrimitive {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    Integrable (fun z => radiusLogPrimitive n (bodyOverlapRoot B z)) volume := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
  have h := ((integrable_negMulLog_uniformBodyDifference hB hpos).add
    (hd.2.2.1.const_mul (1 - Real.log (volume B).toReal))).const_mul
      ((volume B).toReal / (n : ℝ))
  exact h.congr (Filter.Eventually.of_forall fun z =>
    (logPrimitive_eq_scaled_entropy n _ _ _ (bodyOverlapRoot_pow_eq_density hB hpos z)).symm)

theorem integral_bodyRoot_logPrimitive_eq_entropy {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    (∫ z : Fin n → ℝ, radiusLogPrimitive n (bodyOverlapRoot B z)) =
      ((volume B).toReal / (n : ℝ)) *
        (differentialEntropy (crossDifferenceDensity (uniformDensity B) (uniformDensity B)) volume +
          1 - Real.log (volume B).toReal) := by
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
    (isProbabilityDensity_uniformDensity hB.measurableSet hpos hB.measure_ne_top)
  simp_rw [logPrimitive_eq_scaled_entropy n _ _ _ (bodyOverlapRoot_pow_eq_density hB hpos _)]
  rw [integral_const_mul, integral_add (integrable_negMulLog_uniformBodyDifference hB hpos)
    (hd.2.2.1.const_mul _), integral_const_mul, hd.2.2.2]
  unfold differentialEntropy
  ring

/-- Weighted layer cake as a real integral, using the root's bound by one. -/
theorem integral_bodyRoot_kernel {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) (g : ℝ → ℝ)
    (hgint : ∀ r > 0, IntervalIntegrable g volume 0 r)
    (hgnn : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (hF : Integrable (fun z => ∫ t in 0..bodyOverlapRoot B z, g t) volume)
    (hcurve : IntegrableOn (fun t => bodyLevelVolume B t * g t) (Ioo (0 : ℝ) 1) volume) :
    (∫ z : Fin n → ℝ, ∫ t in 0..bodyOverlapRoot B z, g t) =
      ∫ t in Ioo (0 : ℝ) 1, bodyLevelVolume B t * g t := by
  have hgnnAE : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hgnn t ht
  have hc := lintegral_comp_eq_lintegral_meas_le_mul volume
    (Filter.Eventually.of_forall (bodyOverlapRoot_nonneg B))
    (measurable_bodyOverlapRoot hB hpos).aemeasurable hgint hgnnAE
  let L : ℝ → ℝ≥0∞ := fun t => volume (bodyRootLevel B t) * ENNReal.ofReal (g t)
  have hsupp : Function.support ((Ioi (0 : ℝ)).indicator L) ⊆ Ioc 0 1 := by
    intro t ht
    by_contra hn
    apply ht
    by_cases ht0 : 0 < t
    · have ht1 : 1 < t := by
        by_contra h
        exact hn ⟨ht0, le_of_not_gt h⟩
      have he : bodyRootLevel B t = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact (not_le_of_gt ht1) (hz.trans (bodyOverlapRoot_le_one hB hpos z))
      simp [L, he]
    · simp [ht0]
  have hbound : (∫⁻ t in Ioi (0 : ℝ), L t) = ∫⁻ t in Ioo (0 : ℝ) 1, L t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), L t) = ∫⁻ t, (Ioi (0 : ℝ)).indicator L t :=
        (lintegral_indicator measurableSet_Ioi L).symm
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, (Ioi (0 : ℝ)).indicator L t :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, L t := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact Set.indicator_of_mem ht.1 L
      _ = ∫⁻ t in Ioo (0 : ℝ) 1, L t := by
        rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc :
          Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc (0 : ℝ) 1)]
  have hFnn (z : Fin n → ℝ) : 0 ≤ ∫ t in 0..bodyOverlapRoot B z, g t := by
    rw [intervalIntegral.integral_of_le (bodyOverlapRoot_nonneg B z)]
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact hgnn t ht.1
  have hcurvenn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ bodyLevelVolume B t * g t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact mul_nonneg (bodyLevelVolume_nonneg B t) (hgnn t ht.1)
  have he : (∫⁻ t in Ioo (0 : ℝ) 1, L t) =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, bodyLevelVolume B t * g t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hcurve hcurvenn]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [L]
    rw [bodyLevelVolume_eq hB hpos ht.1,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (volume_bodyRootLevel_ne_top hB ht.1)]
  change (∫⁻ z : Fin n → ℝ, ENNReal.ofReal (∫ t in 0..bodyOverlapRoot B z, g t)) =
    ∫⁻ t in Ioi (0 : ℝ), L t at hc
  rw [hbound, he, ← ofReal_integral_eq_lintegral_ofReal hF
    (Filter.Eventually.of_forall hFnn)] at hc
  have hreal := congrArg ENNReal.toReal hc
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hFnn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hcurvenn)] using hreal

theorem bodyPowerLayer_normalization {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    (n : ℝ) * (∫ t in Ioo (0 : ℝ) 1, bodyPowerLayer B t) = (volume B).toReal := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hf : Integrable (fun z : Fin n → ℝ => ∫ t in 0..bodyOverlapRoot B z,
      (n : ℝ) * t ^ (n - 1)) volume := by
    simpa only [integral_pow_derivative n hn] using integrable_bodyRoot_power hB hpos
  have hc : IntegrableOn (fun t => bodyLevelVolume B t * ((n : ℝ) * t ^ (n - 1)))
      (Ioo (0 : ℝ) 1) volume := by
    apply ((integrableOn_bodyPowerLayer hB).const_mul (n : ℝ)).congr
    exact Filter.Eventually.of_forall fun t => by dsimp [bodyPowerLayer]; ring
  have h := integral_bodyRoot_kernel hB hpos (fun t => (n : ℝ) * t ^ (n - 1))
    (fun r _ => (continuous_const.mul (continuous_id.pow _)).intervalIntegrable 0 r)
    (fun t ht => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht.le _)) hf hc
  simp_rw [integral_pow_derivative n hn] at h
  rw [integral_bodyRoot_power hB hpos] at h
  have he : (fun t => bodyLevelVolume B t * ((n : ℝ) * t ^ (n - 1))) =
      (fun t => (n : ℝ) * bodyPowerLayer B t) := by funext t; dsimp [bodyPowerLayer]; ring
  rw [he, integral_const_mul] at h
  exact h.symm

theorem bodyLogLayer_moment {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    (∫ z : Fin n → ℝ, radiusLogPrimitive n (bodyOverlapRoot B z)) =
      (n : ℝ) * ∫ t in Ioo (0 : ℝ) 1, bodyLogLayer B t := by
  have hf : Integrable (fun z : Fin n → ℝ => ∫ t in 0..bodyOverlapRoot B z,
      radiusLogKernel n t) volume := by
    simpa only [integral_radiusLogKernel n (bodyOverlapRoot_nonneg B _)
      (bodyOverlapRoot_le_one hB hpos _)] using integrable_bodyRoot_logPrimitive hB hpos
  have hc : IntegrableOn (fun t => bodyLevelVolume B t * radiusLogKernel n t)
      (Ioo (0 : ℝ) 1) volume := by
    apply ((integrableOn_bodyLogLayer hB).const_mul (n : ℝ)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [radiusLogKernel, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)]
    dsimp [bodyLogLayer, bodyPowerLayer]
    ring
  have h := integral_bodyRoot_kernel hB hpos (radiusLogKernel n)
    (fun r _ => intervalIntegrable_radiusLogKernel n r) (fun t _ => radiusLogKernel_nonneg n t) hf hc
  simp_rw [integral_radiusLogKernel n (bodyOverlapRoot_nonneg B _)
    (bodyOverlapRoot_le_one hB hpos _)] at h
  have he : (∫ t in Ioo (0 : ℝ) 1, bodyLevelVolume B t * radiusLogKernel n t) =
      ∫ t in Ioo (0 : ℝ) 1, (n : ℝ) * bodyLogLayer B t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change bodyLevelVolume B t *
      (Ioc (0 : ℝ) 1).indicator (fun u => (n : ℝ) * u ^ (n - 1) * (-Real.log u)) t = _
    rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)]
    dsimp [bodyLogLayer, bodyPowerLayer]
    ring
  rw [he, integral_const_mul] at h
  exact h

end EntropicRogersShephard
