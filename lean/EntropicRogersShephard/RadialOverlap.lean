import EntropicRogersShephard.BodyDensity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Monoid

/-! Radial Brunn–Minkowski and monotonicity of the normalized superlevel volume. -/

open Real MeasureTheory Set
open scoped ENNReal Pointwise

namespace EntropicRogersShephard

theorem volume_smul_real {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 < c)
    (A : Set (Fin n → ℝ)) : (volume (c • A)).toReal = c ^ n * (volume A).toReal := by
  rw [← Set.image_smul]
  have he : (fun y : Fin n → ℝ => c • y) = AffineMap.homothety (0 : Fin n → ℝ) c := by
    funext y
    simp [AffineMap.homothety_apply]
  rw [he, Measure.addHaar_image_homothety]
  simp [abs_of_nonneg (pow_nonneg hc.le n), ENNReal.toReal_ofReal (pow_nonneg hc.le n)]

theorem volume_root_smul {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 < c)
    (A : Set (Fin n → ℝ)) :
    (volume (c • A)).toReal ^ ((n : ℝ)⁻¹) =
      c * (volume A).toReal ^ ((n : ℝ)⁻¹) := by
  rw [volume_smul_real hc A, Real.mul_rpow (pow_nonneg hc.le n) ENNReal.toReal_nonneg,
    Real.pow_rpow_inv_natCast hc.le (NeZero.ne n)]

/-- A real-volume wrapper around the audited ENNReal Brunn–Minkowski theorem. -/
theorem brunn_minkowski_volume_roots {n : ℕ} [NeZero n] {A B : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    (volume A).toReal ^ ((n : ℝ)⁻¹) + (volume B).toReal ^ ((n : ℝ)⁻¹) ≤
      (volume (A + B)).toReal ^ ((n : ℝ)⁻¹) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hsum := hA.add hB
  have h := brunn_minkowski hAne hA.measurableSet hBne hB.measurableSet hsum.measurableSet
  have hAfinite := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ ((d : ℝ) + 1)⁻¹)
    (hA.measure_ne_top (μ := volume))
  have hBfinite := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ ((d : ℝ) + 1)⁻¹)
    (hB.measure_ne_top (μ := volume))
  have hfinite := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ ((d : ℝ) + 1)⁻¹)
    (hsum.measure_ne_top (μ := volume))
  have hr := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_add hAfinite hBfinite] at hr
  simp only [← ENNReal.toReal_rpow] at hr
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hr

/-- Only concavity along rays toward the origin is needed for the entropy bound. -/
theorem bodyOverlapRoot_radial {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0)
    {z : Fin n → ℝ} (hz : 0 < bodyOverlapRoot B z) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    a * bodyOverlapRoot B z + (1 - a) ≤ bodyOverlapRoot B (a • z) := by
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  have hA := isCompact_bodyOverlap hB z
  have hAne := bodyOverlap_nonempty_of_root_pos hz
  have hBne : B.Nonempty := by
    by_contra h
    exact hpos (by rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty])
  have hsum := (hA.smul a).add (hB.smul (1 - a))
  have hsub : a • bodyOverlap B z + (1 - a) • B ⊆ bodyOverlap B (a • z) := by
    intro u hu
    obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_add.mp hu
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, rfl⟩ := hw
    have hy0 : y ∈ bodyOverlap B 0 := by simpa [bodyOverlap] using hy
    simpa only [smul_zero, add_zero] using
      weighted_mem_bodyOverlap hconv hx hy0 ha.le hb.le (by ring : a + (1 - a) = 1)
  have hbm := brunn_minkowski_volume_roots (hA.smul a) (hB.smul (1 - a))
    (hAne.smul_set (a := a)) (hBne.smul_set (a := 1 - a))
  rw [volume_root_smul ha, volume_root_smul hb] at hbm
  have hvol : (volume (a • bodyOverlap B z + (1 - a) • B)).toReal ≤
      (volume (bodyOverlap B (a • z))).toReal :=
    ENNReal.toReal_mono (isCompact_bodyOverlap hB (a • z)).measure_ne_top (measure_mono hsub)
  have hroot := hbm.trans (Real.rpow_le_rpow ENNReal.toReal_nonneg hvol (by positivity))
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hpos hB.measure_ne_top
  have hvr : 0 < (volume B).toReal ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos hv _
  unfold bodyOverlapRoot
  apply (le_div_iff₀ hvr).mpr
  calc
    _ = a * (volume (bodyOverlap B z)).toReal ^ ((n : ℝ)⁻¹) +
        (1 - a) * (volume B).toReal ^ ((n : ℝ)⁻¹) := by field_simp [hvr.ne']
    _ ≤ _ := hroot

def bodyRootLevel {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {z | t ≤ bodyOverlapRoot B z}

theorem measurableSet_bodyRootLevel {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) (t : ℝ) : MeasurableSet (bodyRootLevel B t) :=
  measurableSet_le measurable_const (measurable_bodyOverlapRoot hB hpos)

theorem bodyRootLevel_subset_support {n : ℕ} [NeZero n] (B : Set (Fin n → ℝ))
    {t : ℝ} (ht : 0 < t) : bodyRootLevel B t ⊆ bodyDifferenceSupport B := by
  intro z hz
  by_contra h
  have he := bodyOverlapRoot_eq_zero_of_not_mem h
  change t ≤ bodyOverlapRoot B z at hz
  rw [he] at hz
  exact (not_le_of_gt ht) hz

theorem volume_bodyRootLevel_ne_top {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) {t : ℝ} (ht : 0 < t) : volume (bodyRootLevel B t) ≠ ∞ :=
  (lt_of_le_of_lt (measure_mono (bodyRootLevel_subset_support B ht))
    (isCompact_bodyDifferenceSupport hB).measure_lt_top).ne

theorem bodyRootLevel_homothety_subset {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht1 : t < 1) :
    ((1 - t) / (1 - s)) • bodyRootLevel B s ⊆ bodyRootLevel B t := by
  have hs1 : s < 1 := hst.trans ht1
  let a := (1 - t) / (1 - s)
  have ha : 0 < a := div_pos (sub_pos.mpr ht1) (sub_pos.mpr hs1)
  have ha1 : a < 1 := (div_lt_one (sub_pos.mpr hs1)).mpr (by linarith)
  intro u hu
  obtain ⟨z, hz, rfl⟩ := hu
  change s ≤ bodyOverlapRoot B z at hz
  have hrad := bodyOverlapRoot_radial hB hconv hpos (hs.trans_le hz) ha ha1
  have he : a * s + (1 - a) = t := by
    dsimp [a]
    field_simp [(sub_pos.mpr hs1).ne']
    <;> ring
  change t ≤ bodyOverlapRoot B (a • z)
  have hmul := mul_le_mul_of_nonneg_left hz ha.le
  linarith

noncomputable def bodyLevelVolumeRatio {n : ℕ} (B : Set (Fin n → ℝ)) (t : ℝ) : ℝ :=
  (volume (bodyRootLevel B t)).toReal / (1 - t) ^ n

theorem monotoneOn_bodyLevelVolumeRatio {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) (hpos : volume B ≠ 0) :
    MonotoneOn (bodyLevelVolumeRatio B) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_refl _
  have ha : 0 < (1 - t) / (1 - s) := div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hs.2)
  have hsub := bodyRootLevel_homothety_subset hB hconv hpos hs.1 hst ht.2
  have hvol := ENNReal.toReal_mono (volume_bodyRootLevel_ne_top hB ht.1) (measure_mono hsub)
  rw [volume_smul_real ha, div_pow, div_mul_eq_mul_div] at hvol
  have h := (div_le_iff₀ (pow_pos (sub_pos.mpr hs.2) n)).mp hvol
  unfold bodyLevelVolumeRatio
  apply (div_le_div_iff₀ (pow_pos (sub_pos.mpr hs.2) n) (pow_pos (sub_pos.mpr ht.2) n)).mpr
  simpa only [mul_comm] using h

end EntropicRogersShephard
