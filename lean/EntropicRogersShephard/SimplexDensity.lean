import EntropicRogersShephard.Density
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! The overlap-radius formula now describes normalized difference densities. -/

open MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem crossDifferenceDensity_uniformDensity {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (z : Fin n → ℝ) :
    crossDifferenceDensity (uniformDensity A) (uniformDensity B) z =
      (volume {x | x ∈ A ∧ x - z ∈ B}).toReal /
        ((volume A).toReal * (volume B).toReal) := by
  have hm : MeasurableSet {x : Fin n → ℝ | x ∈ A ∧ x - z ∈ B} :=
    hA.inter (hB.preimage (measurable_id.sub measurable_const))
  have he : (fun x => uniformDensity A x * uniformDensity B (x - z)) =
      {x | x ∈ A ∧ x - z ∈ B}.indicator
        (fun _ => (volume A).toReal⁻¹ * (volume B).toReal⁻¹) := by
    funext x
    by_cases hx : x ∈ A <;> by_cases hy : x - z ∈ B <;>
      simp [uniformDensity, hx, hy]
  rw [crossDifferenceDensity, he, integral_indicator_const _ hm, smul_eq_mul]
  simp [div_eq_mul_inv, measureReal_def, mul_comm]

/-- Pointwise density formula for all positive scales and all shifts. -/
theorem crossDifferenceDensity_uniformSimplex (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (z : Fin m → ℝ) :
    crossDifferenceDensity (uniformDensity (simplex m a))
        (uniformDensity (simplex m b)) z =
      overlapRadius a b z ^ m /
        (a ^ m * b ^ m * (volume (simplex m 1)).toReal) := by
  rw [crossDifferenceDensity_uniformDensity (isClosed_simplex m a).measurableSet
    (isClosed_simplex m b).measurableSet,
    volume_simplex_overlap, volume_simplex_pos m ha, volume_simplex_pos m hb]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (overlapRadius_nonneg a b z) m),
    ENNReal.toReal_ofReal (pow_nonneg ha.le m),
    ENNReal.toReal_ofReal (pow_nonneg hb.le m)]
  have hv : (volume (simplex m 1)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(volume_unit_simplex_pos m).ne', volume_simplex_ne_top m 1⟩
  field_simp

/-- Normalization without evaluating any simplex volume as a factorial. -/
theorem integral_overlapRadius_pow (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    (∫ z : Fin m → ℝ, overlapRadius a b z ^ m /
      (a ^ m * b ^ m * (volume (simplex m 1)).toReal)) = 1 := by
  simp_rw [← crossDifferenceDensity_uniformSimplex m ha hb]
  exact (isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha)
    (isProbabilityDensity_uniformSimplex m hb)).2.2.2

theorem integrable_overlapRadius_pow (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun z : Fin m → ℝ => overlapRadius a b z ^ m /
      (a ^ m * b ^ m * (volume (simplex m 1)).toReal)) volume := by
  simp_rw [← crossDifferenceDensity_uniformSimplex m ha hb]
  exact (isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha)
    (isProbabilityDensity_uniformSimplex m hb)).2.2.1

theorem crossDifferenceDensity_uniformSimplex_le (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (z : Fin m → ℝ) :
    crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b)) z ≤
        1 / (a ^ m * (volume (simplex m 1)).toReal) := by
  rw [crossDifferenceDensity_uniformSimplex m ha hb]
  have hv : 0 < (volume (simplex m 1)).toReal :=
    ENNReal.toReal_pos (volume_unit_simplex_pos m).ne' (volume_simplex_ne_top m 1)
  have hpow : overlapRadius a b z ^ m ≤ b ^ m :=
    pow_le_pow_left₀ (overlapRadius_nonneg a b z) (overlapRadius_le_right a b z hb.le) m
  have hden : 0 < a ^ m * b ^ m * (volume (simplex m 1)).toReal := by positivity
  apply (div_le_iff₀ hden).mpr
  convert hpow using 1
  field_simp

/-- A compact set containing the support of the simplex difference density. -/
def simplexDifferenceSupport (m : ℕ) (a b : ℝ) : Set (Fin m → ℝ) :=
  (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.1 - p.2) ''
    (simplex m a ×ˢ simplex m b)

theorem isCompact_simplexDifferenceSupport (m : ℕ) (a b : ℝ) :
    IsCompact (simplexDifferenceSupport m a b) :=
  ((isCompact_simplex m a).prod (isCompact_simplex m b)).image
    (continuous_fst.sub continuous_snd)

theorem crossDifferenceDensity_uniformSimplex_eq_zero_of_not_mem (m : ℕ) (a b : ℝ)
    {z : Fin m → ℝ} (hz : z ∉ simplexDifferenceSupport m a b) :
    crossDifferenceDensity (uniformDensity (simplex m a))
      (uniformDensity (simplex m b)) z = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ simplex m a
  · have hy : x - z ∉ simplex m b := by
      intro hy
      exact hz ⟨(x, x - z), ⟨hx, hy⟩, by simp⟩
    simp [uniformDensity, hy]
  · simp [uniformDensity, hx]

theorem integrable_negMulLog_uniformSimplexDifference (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun z => Real.negMulLog
      (crossDifferenceDensity (uniformDensity (simplex m a))
        (uniformDensity (simplex m b)) z)) volume := by
  have hs := isCompact_simplexDifferenceSupport m a b
  apply integrable_negMulLog_of_bounded_support hs.measurableSet hs.measure_ne_top
    (measurable_crossDifferenceDensity
      (measurable_uniformDensity (isClosed_simplex m a).measurableSet)
      (measurable_uniformDensity (isClosed_simplex m b).measurableSet))
  · intro z
    exact ⟨crossDifferenceDensity_nonneg (uniformDensity_nonneg _) (uniformDensity_nonneg _) z,
      crossDifferenceDensity_uniformSimplex_le m ha hb z⟩
  · intro z hz
    exact crossDifferenceDensity_uniformSimplex_eq_zero_of_not_mem m a b hz

/-- Equality on the nonnegative half-line already determines a real polynomial. -/
theorem polynomial_eq_of_eval_eq_nonneg (p q : Polynomial ℝ)
    (h : ∀ s : ℝ, 0 ≤ s → p.eval s = q.eval s) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.Ici_infinite (0 : ℝ)).mono fun s hs => h s hs

/-- Once normalization gives the binomial polynomial, its coefficients are forced.
This theorem does not assume or compute factorial formulas for simplex volumes. -/
theorem coefficients_eq_choose_of_normalization (m : ℕ) (c : ℕ → ℝ)
    (h : ∀ s : ℝ, 0 ≤ s →
      (∑ j ∈ Finset.range (m + 1), c j * s ^ j) = (1 + s) ^ m)
    {j : ℕ} (hj : j ≤ m) : c j = (m.choose j : ℝ) := by
  let p : Polynomial ℝ := ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (c k)
  have hp : p = (1 + Polynomial.X) ^ m := by
    apply polynomial_eq_of_eval_eq_nonneg
    intro s hs
    simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial] using h s hs
  have hc := congrArg (fun r : Polynomial ℝ => r.coeff j) hp
  simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.mem_range, Nat.lt_succ_iff, hj, Polynomial.coeff_one_add_X_pow] using hc

/-- The coefficient step of the symbolic-volume route. The layer-cake identity
in the hypothesis still has to be supplied from the orthant geometry. -/
theorem layer_coefficients_forced_by_normalization (m : ℕ) (c : ℕ → ℝ)
    (h : ∀ s : ℝ, 0 ≤ s →
      (∑ j ∈ Finset.range (m + 1),
        (c j * (m : ℝ) * integerBeta (m - 1) (m - j)) * s ^ j) = (1 + s) ^ m)
    {j : ℕ} (hj : j ≤ m) :
    c j * (m : ℝ) * integerBeta (m - 1) (m - j) = (m.choose j : ℝ) :=
  coefficients_eq_choose_of_normalization m _ h hj

end EntropicRogersShephard
