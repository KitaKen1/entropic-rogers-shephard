import EntropicRogersShephard.ExponentialIntegrability
import EntropicRogersShephard.BoundedDensity

/-! Difference convolution and entropy convergence under exponential domination. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem differenceDensity_exponential_envelope {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hf : IsProbabilityDensity n f) (he : ∀ x, f x ≤ C * Real.exp (-a * ‖x‖)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s, differenceDensity f s ≤ D * Real.exp (-(a / 2) * ‖s‖) := by
  have hi := integrable_exp_neg_mul_norm (n := n) (a := a / 2) (by positivity)
  let I := ∫ x : Fin n → ℝ, Real.exp (-(a / 2) * ‖x‖)
  have hI : 0 ≤ I := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hb : ∀ x, f x ∈ Icc (0 : ℝ) C := by
    intro x
    refine ⟨hf.2.1 x, (he x).trans ?_⟩
    have hexp : Real.exp (-a * ‖x‖) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg x])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hC
  refine ⟨C ^ 2 * I, mul_nonneg (sq_nonneg C) hI, ?_⟩
  intro s
  have hslice := integrable_difference_slice_of_bounded hf hf.1 hb s
  have henv : Integrable (fun x : Fin n → ℝ =>
      (C ^ 2 * Real.exp (-(a / 2) * ‖s‖)) * Real.exp (-(a / 2) * ‖x‖)) volume :=
    hi.const_mul _
  change (∫ x, f x * f (x - s)) ≤ _
  calc
    (∫ x, f x * f (x - s)) ≤ ∫ x,
        (C ^ 2 * Real.exp (-(a / 2) * ‖s‖)) * Real.exp (-(a / 2) * ‖x‖) := by
      apply integral_mono hslice henv
      intro x
      have hnorm : ‖s‖ ≤ ‖x‖ + ‖x - s‖ := by
        calc
          ‖s‖ = ‖x - (x - s)‖ := by congr 1; abel
          _ ≤ ‖x‖ + ‖x - s‖ := norm_sub_le _ _
      calc
        f x * f (x - s) ≤ (C * Real.exp (-a * ‖x‖)) *
            (C * Real.exp (-a * ‖x - s‖)) :=
          mul_le_mul (he x) (he (x - s)) (hf.2.1 _) (mul_nonneg hC (Real.exp_pos _).le)
        _ = C ^ 2 * (Real.exp (-a * ‖x‖) * Real.exp (-a * ‖x - s‖)) := by ring
        _ = C ^ 2 * Real.exp (-a * (‖x‖ + ‖x - s‖)) := by
          rw [← Real.exp_add]
          congr 2 <;> ring
        _ ≤ C ^ 2 * Real.exp (-(a / 2) * ‖s‖ - (a / 2) * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
          apply Real.exp_le_exp.mpr
          nlinarith [norm_nonneg (x - s)]
        _ = (C ^ 2 * Real.exp (-(a / 2) * ‖s‖)) * Real.exp (-(a / 2) * ‖x‖) := by
          simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
          ring
    _ = C ^ 2 * I * Real.exp (-(a / 2) * ‖s‖) := by
      rw [integral_const_mul]
      dsimp [I]
      ring

theorem logconcave_probability_density_entropies_integrable {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume := by
  obtain ⟨a, C, ha, hC, he⟩ := logconcave_probability_density_exponential_envelope hf hl
  obtain ⟨D, hD, hg⟩ := differenceDensity_exponential_envelope ha hC.le hf he
  refine ⟨integrable_negMulLog_of_exponential_envelope ha hC.le hf.1 hf.2.1 he, ?_⟩
  have hd := isProbabilityDensity_differenceDensity hf
  exact integrable_negMulLog_of_exponential_envelope (by positivity : 0 < a / 2) hD
    hd.1 hd.2.1 hg

theorem entropy_tendsto_of_exponential_envelope {n : ℕ} [NeZero n]
    {f : ℕ → (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hm : ∀ j, Measurable (f j))
    (hf : ∀ j x, 0 ≤ f j x) (he : ∀ j x, f j x ≤ C * Real.exp (-a * ‖x‖))
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto (fun j => differentialEntropy (f j) volume) atTop
      (𝓝 (differentialEntropy g volume)) := by
  have h2 := (integrable_exp_neg_mul_norm (n := n) (a := 2 * a) (by positivity)).const_mul (C ^ 2)
  have hh := (integrable_exp_neg_mul_norm (n := n) (a := a / 2) (by positivity)).const_mul
    (2 * Real.sqrt C)
  apply tendsto_integral_of_dominated_convergence
    (fun x : Fin n → ℝ => C ^ 2 * Real.exp (-(2 * a) * ‖x‖) +
      2 * Real.sqrt C * Real.exp (-(a / 2) * ‖x‖))
    (fun j => (Real.continuous_negMulLog.measurable.comp (hm j)).aestronglyMeasurable)
    (h2.add hh)
  · intro j
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        entropy_exponential_envelope hC (hf j) (he j) x)
  · filter_upwards [hlim] with x hx
    exact Real.continuous_negMulLog.continuousAt.tendsto.comp hx

end EntropicRogersShephard
