import EntropicRogersShephard.BodyMoments
import EntropicRogersShephard.WeightedTilt

/-! The entropy increment of a uniform convex body is at most F(n). -/

open Real MeasureTheory Set
open scoped ENNReal

namespace EntropicRogersShephard

theorem integerBeta_pos (a b : ℕ) : 0 < integerBeta a b := by
  have ha : 0 < (a.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos a
  have hb : 0 < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
  have hd : 0 < ((a + b + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_pos (mul_pos ha hb) hd

theorem integral_beta_Ioo (a b : ℕ) :
    (∫ t : ℝ in Ioo 0 1, t ^ a * (1 - t) ^ b) = integerBeta a b := by
  simpa only [betaMoment, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using betaMoment_eq_integerBeta a b

theorem integral_log_beta_Ioo (a b : ℕ) :
    (∫ t : ℝ in Ioo 0 1, (-Real.log t) * (t ^ a * (1 - t) ^ b)) =
      integerBeta a b * (H (a + b + 1) - H a) := by
  have he : (fun t : ℝ => (-Real.log t) * (t ^ a * (1 - t) ^ b)) =
      (fun t : ℝ => t ^ a * (1 - t) ^ b * (-Real.log t)) := by funext t; ring
  rw [he]
  simpa only [betaLogMoment, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using betaLogMoment_eq_harmonic a b

/-- The increasing level-volume ratio lowers the logarithmic Beta mean. -/
theorem body_log_layer_mean_bound {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0) :
    (∫ t in Ioo (0 : ℝ) 1, bodyLogLayer B t) ≤
      (∫ t in Ioo (0 : ℝ) 1, bodyPowerLayer B t) * (H (2 * n) - H (n - 1)) := by
  let w : ℝ → ℝ := fun t => t ^ (n - 1) * (1 - t) ^ n
  have hw : Integrable w (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (intervalIntegrable_betaMoment (n - 1) n).1.mono_set Ioo_subset_Ioc_self
  have hlw : Integrable (fun t : ℝ => (-Real.log t) * w t)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply ((intervalIntegrable_betaLogMoment (n - 1) n).1.mono_set Ioo_subset_Ioc_self).congr
    exact Filter.Eventually.of_forall fun t => by dsimp [w]; ring
  have hwnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ w t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (pow_nonneg (sub_pos.mpr ht.2).le _)
  have hlanti : AntitoneOn (fun t : ℝ => -Real.log t) (Ioo (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact neg_le_neg (Real.log_le_log hs.1 hst)
  have h := weighted_integral_mul_le_product_of_monotone_antitone
    (r := bodyLevelTilt B) (l := fun t : ℝ => -Real.log t) (w := w)
    (self_mem_ae_restrict measurableSet_Ioo) hwnn hw (integrable_bodyTilt_beta hB) hlw
    (integrable_bodyTilt_log_beta hB) (monotoneOn_bodyLevelTilt hB hconv hpos) hlanti
  have hR : (∫ t in Ioo (0 : ℝ) 1, bodyLevelTilt B t * w t) =
      ∫ t in Ioo (0 : ℝ) 1, bodyPowerLayer B t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [w, bodyLevelTilt, bodyPowerLayer]
    field_simp [(pow_pos (sub_pos.mpr ht.2) n).ne']
  have hA : (∫ t in Ioo (0 : ℝ) 1, bodyLevelTilt B t * (-Real.log t) * w t) =
      ∫ t in Ioo (0 : ℝ) 1, bodyLogLayer B t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [w, bodyLevelTilt, bodyLogLayer, bodyPowerLayer]
    field_simp [(pow_pos (sub_pos.mpr ht.2) n).ne']
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hidx : n - 1 + n + 1 = 2 * n := by omega
  change (∫ t in Ioo (0 : ℝ) 1, w t) *
      (∫ t in Ioo (0 : ℝ) 1, bodyLevelTilt B t * (-Real.log t) * w t) ≤
        (∫ t in Ioo (0 : ℝ) 1, bodyLevelTilt B t * w t) *
          (∫ t in Ioo (0 : ℝ) 1, (-Real.log t) * w t) at h
  rw [hR, hA] at h
  dsimp only [w] at h
  rw [integral_beta_Ioo, integral_log_beta_Ioo, hidx] at h
  apply (mul_le_mul_iff_left₀ (integerBeta_pos (n - 1) n)).mp
  convert h using 1 <;> ring

theorem body_log_primitive_upper_bound {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0) :
    (∫ z : Fin n → ℝ, radiusLogPrimitive n (bodyOverlapRoot B z)) ≤
      (volume B).toReal * (H (2 * n) - H (n - 1)) := by
  rw [bodyLogLayer_moment hB hpos]
  calc
    _ ≤ (n : ℝ) * ((∫ t in Ioo (0 : ℝ) 1, bodyPowerLayer B t) *
        (H (2 * n) - H (n - 1))) :=
      mul_le_mul_of_nonneg_left (body_log_layer_mean_bound hB hconv hpos) (Nat.cast_nonneg n)
    _ = _ := by rw [← mul_assoc, bodyPowerLayer_normalization hB hpos]

/-- The actual density-form convex-body entropy increment, in every positive dimension. -/
theorem uniform_convex_body_entropy_bound {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0) :
    differentialEntropy (crossDifferenceDensity (uniformDensity B) (uniformDensity B)) volume -
      differentialEntropy (uniformDensity B) volume ≤ F n := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let V := (volume B).toReal
  have hv : 0 < V := ENNReal.toReal_pos hpos hB.measure_ne_top
  have h := body_log_primitive_upper_bound hB hconv hpos
  rw [integral_bodyRoot_logPrimitive_eq_entropy hB hpos] at h
  have he := mul_le_mul_of_nonneg_left h (div_pos hn hv).le
  have hleft (x : ℝ) : (n : ℝ) / V * (V / (n : ℝ) * x) = x := by field_simp [hn.ne', hv.ne']
  have hright (x : ℝ) : (n : ℝ) / V * (V * x) = (n : ℝ) * x := by field_simp [hv.ne']
  change (n : ℝ) / V * (V / (n : ℝ) *
      (differentialEntropy (crossDifferenceDensity (uniformDensity B) (uniformDensity B)) volume +
        1 - Real.log V)) ≤ (n : ℝ) / V * (V * (H (2 * n) - H (n - 1))) at he
  rw [hleft, hright] at he
  have hnat : n - 1 + 1 = n := by
    have hnp : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnat
  have hH : H n = H (n - 1) + 1 / (n : ℝ) := by
    have hs := H_succ (n - 1)
    rwa [hnat, hcast] at hs
  have hF : F n = (n : ℝ) * (H (2 * n) - H (n - 1)) - 1 := by
    rw [F, hH]
    field_simp [hn.ne']
    <;> ring
  rw [differentialEntropy_uniformDensity hB.measurableSet hpos hB.measure_ne_top, hF]
  change differentialEntropy (crossDifferenceDensity (uniformDensity B) (uniformDensity B)) volume -
    Real.log V ≤ _
  linarith

end EntropicRogersShephard
