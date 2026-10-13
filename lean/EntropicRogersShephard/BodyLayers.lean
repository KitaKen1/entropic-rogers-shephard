import EntropicRogersShephard.RadialOverlap
import EntropicRogersShephard.LayerLogMoments
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Measurable and integrable layer volumes, using the finite difference support. -/

open Real MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace EntropicRogersShephard

/-- Restrict before taking real values, so even the nonpositive levels have finite volume. -/
noncomputable def bodyLevelVolume {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : ℝ :=
  ((volume.restrict (bodyDifferenceSupport B)) (bodyRootLevel B t)).toReal

theorem bodyLevelVolume_nonneg {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) :
    0 ≤ bodyLevelVolume B t := ENNReal.toReal_nonneg

theorem bodyLevelVolume_eq {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) {t : ℝ} (ht : 0 < t) :
    bodyLevelVolume B t = (volume (bodyRootLevel B t)).toReal := by
  rw [bodyLevelVolume, Measure.restrict_apply (measurableSet_bodyRootLevel hB hpos t),
    Set.inter_eq_left.mpr (bodyRootLevel_subset_support B ht)]

theorem antitone_bodyLevelVolume {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    Antitone (bodyLevelVolume B) := by
  let ν := volume.restrict (bodyDifferenceSupport B)
  have hν : ν univ < ∞ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_bodyDifferenceSupport hB).measure_lt_top
  intro s t hst
  have hfin : ν (bodyRootLevel B s) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (subset_univ _)) hν).ne
  apply ENNReal.toReal_mono hfin
  apply measure_mono
  intro z hz
  exact hst.trans hz

theorem measurable_bodyLevelVolume {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    Measurable (bodyLevelVolume B) := (antitone_bodyLevelVolume hB).measurable

theorem bodyLevelVolume_le_support {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B)
    (t : ℝ) : bodyLevelVolume B t ≤ (volume (bodyDifferenceSupport B)).toReal := by
  let ν := volume.restrict (bodyDifferenceSupport B)
  have hν : ν univ ≠ ∞ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_bodyDifferenceSupport hB).measure_ne_top
  have h : (ν (bodyRootLevel B t)).toReal ≤ (ν univ).toReal :=
    ENNReal.toReal_mono hν (measure_mono (subset_univ _))
  simpa only [ν, Measure.restrict_apply_univ, bodyLevelVolume] using h

noncomputable def bodyLevelTilt {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : ℝ :=
  bodyLevelVolume B t / (1 - t) ^ n

theorem measurable_bodyLevelTilt {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    Measurable (bodyLevelTilt B) :=
  (measurable_bodyLevelVolume hB).div (by fun_prop)

theorem monotoneOn_bodyLevelTilt {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0) :
    MonotoneOn (bodyLevelTilt B) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  have h := monotoneOn_bodyLevelVolumeRatio hB hconv hpos hs ht hst
  simpa only [bodyLevelTilt, bodyLevelVolume_eq hB hpos hs.1,
    bodyLevelVolume_eq hB hpos ht.1, bodyLevelVolumeRatio] using h

noncomputable def bodyPowerLayer {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : ℝ :=
  bodyLevelVolume B t * t ^ (n - 1)

noncomputable def bodyLogLayer {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : ℝ :=
  bodyPowerLayer B t * (-Real.log t)

theorem bodyPowerLayer_nonneg {n : ℕ} (B : Set (Fin n → ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ bodyPowerLayer B t := mul_nonneg (bodyLevelVolume_nonneg B t) (pow_nonneg ht _)

theorem bodyPowerLayer_le_support {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    bodyPowerLayer B t ≤ (volume (bodyDifferenceSupport B)).toReal := by
  have hp : t ^ (n - 1) ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
  calc
    bodyPowerLayer B t ≤ bodyLevelVolume B t * 1 :=
      mul_le_mul_of_nonneg_left hp (bodyLevelVolume_nonneg B t)
    _ ≤ _ := by rw [mul_one]; exact bodyLevelVolume_le_support hB t

theorem integrableOn_bodyPowerLayer {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    IntegrableOn (bodyPowerLayer B) (Ioo (0 : ℝ) 1) volume := by
  have hc : IntegrableOn (fun _ : ℝ => (volume (bodyDifferenceSupport B)).toReal)
      (Ioo (0 : ℝ) 1) volume := integrableOn_const (by simp)
  apply hc.mono' (((measurable_bodyLevelVolume hB).mul
    (measurable_id.pow_const (n - 1))).aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  change ‖bodyPowerLayer B t‖ ≤ (volume (bodyDifferenceSupport B)).toReal
  rw [Real.norm_eq_abs, abs_of_nonneg (bodyPowerLayer_nonneg B ht.1.le)]
  exact bodyPowerLayer_le_support hB ht

theorem integrableOn_bodyLogLayer {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    IntegrableOn (bodyLogLayer B) (Ioo (0 : ℝ) 1) volume := by
  let C := (volume (bodyDifferenceSupport B)).toReal
  have hl : IntegrableOn (fun t : ℝ => -Real.log t) (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_log'.neg : IntervalIntegrable (fun t : ℝ => -Real.log t) volume 0 1).1.mono_set
      Ioo_subset_Ioc_self
  have hm : Measurable (bodyLogLayer B) :=
    ((measurable_bodyLevelVolume hB).mul (measurable_id.pow_const (n - 1))).mul
      Real.measurable_log.neg
  apply (hl.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hlog : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2.le)
  change ‖bodyPowerLayer B t * (-Real.log t)‖ ≤ C * (-Real.log t)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bodyPowerLayer_nonneg B ht.1.le) hlog)]
  exact mul_le_mul_of_nonneg_right (bodyPowerLayer_le_support hB ht) hlog

theorem integrable_bodyTilt_beta {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    Integrable (fun t : ℝ => bodyLevelTilt B t * (t ^ (n - 1) * (1 - t) ^ n))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (integrableOn_bodyPowerLayer hB).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  dsimp [bodyPowerLayer, bodyLevelTilt]
  field_simp [(pow_pos (sub_pos.mpr ht.2) n).ne']

theorem integrable_bodyTilt_log_beta {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    Integrable (fun t : ℝ => bodyLevelTilt B t * (-Real.log t) *
      (t ^ (n - 1) * (1 - t) ^ n)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (integrableOn_bodyLogLayer hB).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  dsimp [bodyLogLayer, bodyPowerLayer, bodyLevelTilt]
  field_simp [(pow_pos (sub_pos.mpr ht.2) n).ne']

end EntropicRogersShephard
