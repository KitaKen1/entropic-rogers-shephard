import EntropicRogersShephard.SimplexDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Uniform-body difference densities and their normalized overlap roots. -/

open Real MeasureTheory Set
open scoped ENNReal Pointwise

namespace EntropicRogersShephard

def bodyDifferenceSupport {n : ℕ} (B : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (B ×ˢ B)

theorem isCompact_bodyDifferenceSupport {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) :
    IsCompact (bodyDifferenceSupport B) :=
  (hB.prod hB).image (continuous_fst.sub continuous_snd)

theorem uniformBodyDifference_eq_zero_of_not_mem {n : ℕ} {B : Set (Fin n → ℝ)}
    {z : Fin n → ℝ} (hz : z ∉ bodyDifferenceSupport B) :
    crossDifferenceDensity (uniformDensity B) (uniformDensity B) z = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ B
  · have hy : x - z ∉ B := by
      intro hy
      exact hz ⟨(x, x - z), ⟨hx, hy⟩, by simp⟩
    simp [uniformDensity, hy]
  · simp [uniformDensity, hx]

theorem uniformBodyDifference_eq_overlap {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) (z : Fin n → ℝ) :
    crossDifferenceDensity (uniformDensity B) (uniformDensity B) z =
      (volume (bodyOverlap B z)).toReal / (volume B).toReal ^ 2 := by
  simpa only [bodyOverlap, pow_two] using crossDifferenceDensity_uniformDensity hB hB z

theorem uniformBodyDifference_le {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) (z : Fin n → ℝ) :
    crossDifferenceDensity (uniformDensity B) (uniformDensity B) z ≤ (volume B).toReal⁻¹ := by
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hpos hB.measure_ne_top
  have hsub : bodyOverlap B z ⊆ B := fun _ hx => hx.1
  have hvol : (volume (bodyOverlap B z)).toReal ≤ (volume B).toReal :=
    ENNReal.toReal_mono hB.measure_ne_top (measure_mono hsub)
  rw [uniformBodyDifference_eq_overlap hB.measurableSet]
  apply (div_le_iff₀ (pow_pos hv 2)).mpr
  calc
    (volume (bodyOverlap B z)).toReal ≤ (volume B).toReal := hvol
    _ = (volume B).toReal⁻¹ * (volume B).toReal ^ 2 := by field_simp

theorem integrable_negMulLog_uniformBodyDifference {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) :
    Integrable (fun z => Real.negMulLog
      (crossDifferenceDensity (uniformDensity B) (uniformDensity B) z)) volume := by
  have hD := isCompact_bodyDifferenceSupport hB
  apply integrable_negMulLog_of_bounded_support hD.measurableSet hD.measure_ne_top
    (measurable_crossDifferenceDensity (measurable_uniformDensity hB.measurableSet)
      (measurable_uniformDensity hB.measurableSet))
  · intro z
    exact ⟨crossDifferenceDensity_nonneg (uniformDensity_nonneg B) (uniformDensity_nonneg B) z,
      uniformBodyDifference_le hB hpos z⟩
  · intro z hz
    exact uniformBodyDifference_eq_zero_of_not_mem hz

/-- Ratio of volume roots; the denominator is positive for the bodies used below. -/
noncomputable def bodyOverlapRoot {n : ℕ} (B : Set (Fin n → ℝ)) (z : Fin n → ℝ) : ℝ :=
  (volume (bodyOverlap B z)).toReal ^ ((n : ℝ)⁻¹) /
    (volume B).toReal ^ ((n : ℝ)⁻¹)

theorem bodyOverlapRoot_nonneg {n : ℕ} (B : Set (Fin n → ℝ)) (z : Fin n → ℝ) :
    0 ≤ bodyOverlapRoot B z :=
  div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem bodyOverlapRoot_pow {n : ℕ} [NeZero n] (B : Set (Fin n → ℝ)) (z : Fin n → ℝ) :
    bodyOverlapRoot B z ^ n = (volume (bodyOverlap B z)).toReal / (volume B).toReal := by
  rw [bodyOverlapRoot, div_pow,
    Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg (NeZero.ne n),
    Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg (NeZero.ne n)]

theorem bodyOverlapRoot_pow_eq_density {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) (z : Fin n → ℝ) :
    bodyOverlapRoot B z ^ n = (volume B).toReal *
      crossDifferenceDensity (uniformDensity B) (uniformDensity B) z := by
  have hv : (volume B).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos, hB.measure_ne_top⟩
  rw [bodyOverlapRoot_pow, uniformBodyDifference_eq_overlap hB.measurableSet]
  field_simp

theorem bodyOverlapRoot_zero {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) : bodyOverlapRoot B 0 = 1 := by
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hpos hB.measure_ne_top
  rw [bodyOverlapRoot, bodyOverlap_zero, div_self (Real.rpow_pos_of_pos hv _).ne']

theorem bodyOverlapRoot_le_one {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) (z : Fin n → ℝ) : bodyOverlapRoot B z ≤ 1 := by
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hpos hB.measure_ne_top
  have hsub : bodyOverlap B z ⊆ B := fun _ hx => hx.1
  have hvol : (volume (bodyOverlap B z)).toReal ≤ (volume B).toReal :=
    ENNReal.toReal_mono hB.measure_ne_top (measure_mono hsub)
  exact (div_le_one (Real.rpow_pos_of_pos hv _)).mpr
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hvol (by positivity))

theorem bodyOverlapRoot_eq_zero_of_not_mem {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    {z : Fin n → ℝ} (hz : z ∉ bodyDifferenceSupport B) : bodyOverlapRoot B z = 0 := by
  have hempty : bodyOverlap B z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hz ⟨(x, x - z), hx, by simp⟩
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp [bodyOverlapRoot, hempty, Real.zero_rpow (inv_ne_zero hn)]

theorem bodyOverlap_nonempty_of_root_pos {n : ℕ} [NeZero n] {B : Set (Fin n → ℝ)}
    {z : Fin n → ℝ} (hz : 0 < bodyOverlapRoot B z) : (bodyOverlap B z).Nonempty := by
  by_contra h
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hempty := Set.not_nonempty_iff_eq_empty.mp h
  have he : bodyOverlapRoot B z = 0 := by
    simp [bodyOverlapRoot, hempty, Real.zero_rpow (inv_ne_zero hn)]
  exact hz.ne' he

theorem measurable_bodyOverlapRoot {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hpos : volume B ≠ 0) : Measurable (bodyOverlapRoot B) := by
  have hv : (volume B).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos, hB.measure_ne_top⟩
  have he : (fun z => (volume (bodyOverlap B z)).toReal) =
      (fun z => crossDifferenceDensity (uniformDensity B) (uniformDensity B) z *
        (volume B).toReal ^ 2) := by
    funext z
    rw [uniformBodyDifference_eq_overlap hB.measurableSet]
    field_simp
  have hm : Measurable (fun z => (volume (bodyOverlap B z)).toReal) := by
    rw [he]
    exact (measurable_crossDifferenceDensity (measurable_uniformDensity hB.measurableSet)
      (measurable_uniformDensity hB.measurableSet)).mul_const _
  exact ((Real.continuous_rpow_const (by positivity : 0 ≤ (n : ℝ)⁻¹)).measurable.comp hm).div_const _

end EntropicRogersShephard
