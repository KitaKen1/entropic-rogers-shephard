import EntropicRogersShephard.ProductDensity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The unit one-sided exponential, its actual difference density, and both entropies. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def oneSidedExponential : ℝ → ℝ := (Ici 0).indicator (fun t => Real.exp (-t))

noncomputable def unitLaplace : ℝ → ℝ := fun t => Real.exp (-|t|) / 2

theorem measurable_oneSidedExponential : Measurable oneSidedExponential :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (-t))).indicator measurableSet_Ici

theorem oneSidedExponential_nonneg (t : ℝ) : 0 ≤ oneSidedExponential t :=
  Set.indicator_nonneg (fun x _ => (Real.exp_pos _).le) t

theorem oneSidedExponential_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    oneSidedExponential t = Real.exp (-t) := Set.indicator_of_mem ht _

theorem oneSidedExponential_of_neg {t : ℝ} (ht : t < 0) : oneSidedExponential t = 0 :=
  Set.indicator_of_notMem (not_le.mpr ht) _

theorem integrable_oneSidedExponential : Integrable oneSidedExponential volume := by
  rw [oneSidedExponential, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_neg_Ioi 0

theorem integral_oneSidedExponential : (∫ t, oneSidedExponential t) = 1 := by
  rw [oneSidedExponential, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi_zero]

theorem scalarLogConcave_oneSidedExponential : ScalarLogConcave oneSidedExponential := by
  intro x y a b ha hb hab
  simp only [Real.rpow_eq_pow]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hz : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
      rw [oneSidedExponential_of_nonneg hx, oneSidedExponential_of_nonneg hy,
        oneSidedExponential_of_nonneg hz, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      apply le_of_eq
      congr 1
      ring
    · rw [oneSidedExponential_of_neg (lt_of_not_ge hy), Real.zero_rpow hb0, mul_zero]
      exact oneSidedExponential_nonneg _
  · rw [oneSidedExponential_of_neg (lt_of_not_ge hx), Real.zero_rpow ha0, zero_mul]
    exact oneSidedExponential_nonneg _

theorem integrable_comp_abs_of_integrableOn {h : ℝ → ℝ}
    (hh : IntegrableOn h (Ioi 0) volume) : Integrable (fun t => h |t|) volume := by
  have hc : IntegrableOn h (Ici 0) volume := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hh
  have hneg := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := h) (s := Ici 0)).mpr hc
  have hs : (fun x : ℝ => -x) ⁻¹' Ici 0 = Iic 0 := by ext x; simp
  rw [hs] at hneg
  have hn : IntegrableOn (fun t => h |t|) (Iic 0) volume := by
    apply hneg.congr_fun _ measurableSet_Iic
    intro x hx
    change h (-x) = h |x|
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
  have hp : IntegrableOn (fun t => h |t|) (Ioi 0) volume := by
    apply hh.congr_fun _ measurableSet_Ioi
    intro x hx
    change h x = h |x|
    rw [abs_of_pos (show 0 < x from hx)]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hn, hp⟩

theorem integrableOn_exponential_first_moment :
    IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
    (b := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [Real.rpow_one, neg_one_mul] using h

theorem integral_exponential_first_moment :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 := by
  have hg : Real.Gamma (2 : ℝ) = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := (1 : ℝ))
    (by norm_num) (by norm_num)
  norm_num [Real.rpow_one, hg] at h
  exact h

theorem oneSidedExponential_entropy :
    Integrable (fun t => Real.negMulLog (oneSidedExponential t)) volume ∧
      differentialEntropy oneSidedExponential volume = 1 := by
  have he : (fun t => Real.negMulLog (oneSidedExponential t)) =
      (Ici 0).indicator (fun t => t * Real.exp (-t)) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [oneSidedExponential_of_nonneg ht, Set.indicator_of_mem (s := Ici 0) ht]
      simp only [Real.negMulLog_def, Real.log_exp]
      ring
    · rw [oneSidedExponential_of_neg (lt_of_not_ge ht), Set.indicator_of_notMem (s := Ici 0) ht,
        Real.negMulLog_zero]
  have hi : Integrable (fun t => Real.negMulLog (oneSidedExponential t)) volume := by
    rw [he, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exponential_first_moment
  refine ⟨hi, ?_⟩
  change (∫ t, Real.negMulLog (oneSidedExponential t)) = 1
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exponential_first_moment]

theorem integrable_unitLaplace : Integrable unitLaplace volume := by
  have h : Integrable (fun t : ℝ => Real.exp (-|t|)) volume := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_abs (a := (1 : ℝ)) (by norm_num)
  exact h.div_const 2

theorem integral_unitLaplace : (∫ t, unitLaplace t) = 1 := by
  have habs : (∫ t : ℝ, Real.exp (-|t|)) = 2 * ∫ t : ℝ in Ioi 0, Real.exp (-t) :=
    integral_comp_abs (f := fun t : ℝ => Real.exp (-t))
  change (∫ t, Real.exp (-|t|) / 2) = 1
  rw [integral_div, habs, integral_exp_neg_Ioi_zero]
  norm_num

theorem unitLaplace_first_moment :
    Integrable (fun t => unitLaplace t * |t|) volume ∧
      (∫ t, unitLaplace t * |t|) = 1 := by
  have he : (fun t => unitLaplace t * |t|) =
      (fun t => (|t| * Real.exp (-|t|)) / 2) := by
    funext t
    dsimp [unitLaplace]
    ring
  have hi := (integrable_comp_abs_of_integrableOn integrableOn_exponential_first_moment).div_const 2
  have habs : (∫ t : ℝ, |t| * Real.exp (-|t|)) =
      2 * ∫ t : ℝ in Ioi 0, t * Real.exp (-t) :=
    integral_comp_abs (f := fun t : ℝ => t * Real.exp (-t))
  rw [he]
  refine ⟨hi, ?_⟩
  rw [integral_div, habs, integral_exponential_first_moment]
  norm_num

theorem unitLaplace_entropy :
    Integrable (fun t => Real.negMulLog (unitLaplace t)) volume ∧
      differentialEntropy unitLaplace volume = 1 + Real.log 2 := by
  have he : (fun t => Real.negMulLog (unitLaplace t)) =
      (fun t => Real.log 2 * unitLaplace t + unitLaplace t * |t|) := by
    funext t
    simp only [unitLaplace, Real.negMulLog_def,
      Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp]
    ring
  have hi := integrable_unitLaplace.const_mul (Real.log 2)
  have hm := unitLaplace_first_moment.1
  have hh : Integrable (fun t => Real.negMulLog (unitLaplace t)) volume := by
    rw [he]
    exact hi.add hm
  refine ⟨hh, ?_⟩
  change (∫ t, Real.negMulLog (unitLaplace t)) = _
  rw [he, integral_add hi hm, integral_const_mul, integral_unitLaplace,
    unitLaplace_first_moment.2]
  ring

theorem oneSidedExponential_difference_kernel (s x : ℝ) :
    oneSidedExponential x * oneSidedExponential (x - s) =
      (Ici (max 0 s)).indicator (fun t => Real.exp s * Real.exp (-2 * t)) x := by
  by_cases hx : max 0 s ≤ x
  · have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
    have hxs : 0 ≤ x - s := sub_nonneg.mpr ((le_max_right _ _).trans hx)
    rw [oneSidedExponential_of_nonneg hx0, oneSidedExponential_of_nonneg hxs,
      Set.indicator_of_mem (s := Ici (max 0 s)) hx, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · rw [Set.indicator_of_notMem (s := Ici (max 0 s)) hx]
    by_cases hx0 : 0 ≤ x
    · have hxs : x - s < 0 := by
        have hs : ¬ s ≤ x := by intro hs; exact hx (max_le hx0 hs)
        linarith
      rw [oneSidedExponential_of_neg hxs, mul_zero]
    · rw [oneSidedExponential_of_neg (lt_of_not_ge hx0), zero_mul]

theorem integral_oneSidedExponential_difference (s : ℝ) :
    (∫ x, oneSidedExponential x * oneSidedExponential (x - s)) = unitLaplace s := by
  simp_rw [oneSidedExponential_difference_kernel]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
  have hexp : s + -2 * max 0 s = -|s| := by
    by_cases hs : 0 ≤ s
    · rw [max_eq_right hs, abs_of_nonneg hs]
      ring
    · rw [max_eq_left (not_le.mp hs).le, abs_of_neg (not_le.mp hs)]
      ring
  change Real.exp s * (-Real.exp (-2 * max 0 s) / -2) = Real.exp (-|s|) / 2
  rw [← hexp, Real.exp_add]
  ring

end EntropicRogersShephard
