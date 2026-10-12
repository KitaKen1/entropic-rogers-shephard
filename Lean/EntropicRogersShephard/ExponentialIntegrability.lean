/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The one-dimensional lemma follows the half-line route in TauCeti's ExpDecay.lean.
-/
import EntropicRogersShephard.ExponentialTails
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi

/-! Exponential domination and an integrable envelope for the entropy integrand. -/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) volume := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    change Real.exp (a * x) = Real.exp (-a * |x|)
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  · apply (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    change Real.exp (-a * x) = Real.exp (-a * |x|)
    rw [abs_of_pos (show 0 < x from hx)]

theorem integrable_exp_neg_mul_norm {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-a * ‖x‖)) volume := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  let b := a / (n : ℝ)
  have hb : 0 < b := div_pos ha hn
  have hi : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-b * |x i|)) volume :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_abs hb)
  apply hi.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hs : ∑ i : Fin n, |x i| ≤ (n : ℝ) * ‖x‖ := by
    simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
      Pi.sum_norm_apply_le_norm x
  have hbn : b * (n : ℝ) = a := div_mul_cancel₀ _ hn.ne'
  have hmul := mul_le_mul_of_nonneg_left hs hb.le
  rw [← mul_assoc, hbn] at hmul
  rw [← Finset.mul_sum]
  linarith

theorem abs_negMulLog_le_square_add_sqrt {t : ℝ} (ht : 0 ≤ t) :
    |Real.negMulLog t| ≤ t ^ 2 + 2 * Real.sqrt t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  by_cases ht1 : t ≤ 1
  · have hlog := (Real.abs_log_mul_self_rpow_lt t (1 / 2) ht ht1 (by norm_num)).le
    rw [← Real.sqrt_eq_rpow] at hlog
    norm_num at hlog
    have hh := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg t)
    have he : |Real.log t| * |Real.sqrt t| * Real.sqrt t = |Real.negMulLog t| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg t), mul_assoc,
        ← pow_two, Real.sq_sqrt ht.le]
      simp only [Real.negMulLog_def, abs_mul, abs_neg, abs_of_pos ht]
      ring
    rw [he] at hh
    exact hh.trans (by nlinarith [sq_nonneg t])
  · have h1 : 1 ≤ t := (lt_of_not_ge ht1).le
    have hlog := Real.log_le_sub_one_of_pos ht
    have he : |Real.negMulLog t| = t * Real.log t := by
      simp only [Real.negMulLog_def, abs_mul, abs_neg, abs_of_pos ht,
        abs_of_nonneg (Real.log_nonneg h1)]
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlog ht.le, Real.sqrt_nonneg t]

theorem sqrt_exp_eq (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

theorem entropy_exponential_envelope {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {a C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, 0 ≤ f x)
    (he : ∀ x, f x ≤ C * Real.exp (-a * ‖x‖)) (x : Fin n → ℝ) :
    |Real.negMulLog (f x)| ≤
      C ^ 2 * Real.exp (-(2 * a) * ‖x‖) +
      2 * Real.sqrt C * Real.exp (-(a / 2) * ‖x‖) := by
  have hsq := (sq_le_sq₀ (hf x) (mul_nonneg hC (Real.exp_pos _).le)).mpr (he x)
  have hroot := Real.sqrt_le_sqrt (he x)
  have he2 : (C * Real.exp (-a * ‖x‖)) ^ 2 = C ^ 2 * Real.exp (-(2 * a) * ‖x‖) := by
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have heroot : Real.sqrt (C * Real.exp (-a * ‖x‖)) =
      Real.sqrt C * Real.exp (-(a / 2) * ‖x‖) := by
    rw [Real.sqrt_mul hC, sqrt_exp_eq]
    congr 2
    ring
  rw [he2] at hsq
  rw [heroot] at hroot
  exact (abs_negMulLog_le_square_add_sqrt (hf x)).trans (by linarith)

theorem integrable_negMulLog_of_exponential_envelope {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (he : ∀ x, f x ≤ C * Real.exp (-a * ‖x‖)) :
    Integrable (fun x => Real.negMulLog (f x)) volume := by
  have h2 := (integrable_exp_neg_mul_norm (n := n) (a := 2 * a) (by positivity)).const_mul (C ^ 2)
  have hh := (integrable_exp_neg_mul_norm (n := n) (a := a / 2) (by positivity)).const_mul
    (2 * Real.sqrt C)
  apply (h2.add hh).mono' (Real.continuous_negMulLog.measurable.comp hm).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply] using
    entropy_exponential_envelope hC hf he x

theorem integrable_negMulLog_logconcave_probability_density {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    Integrable (fun x => Real.negMulLog (f x)) volume := by
  obtain ⟨a, C, ha, hC, he⟩ := logconcave_probability_density_exponential_envelope hf hl
  exact integrable_negMulLog_of_exponential_envelope ha hC.le hf.1 hf.2.1 he

end EntropicRogersShephard
