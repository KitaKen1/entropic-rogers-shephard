import EntropicRogersShephard.GeneralDensityBound
import EntropicRogersShephard.DensityMeasure
import Mathlib.Probability.HasLaw

/-! Connect the actual difference density to the law of independent random vectors. -/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal MeasureTheory

namespace EntropicRogersShephard

theorem map_neg_realDensityMeasure {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    (realDensityMeasure volume f).map (fun x => -x) =
      realDensityMeasure volume (fun x => f (-x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hφn : Measurable (fun x => φ (-x)) := hφ.comp measurable_neg
  have hfn : Measurable (fun x => f (-x)) := hf.comp measurable_neg
  simp only [realDensityMeasure]
  rw [lintegral_map hφ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume hf.ennreal_ofReal hφn,
    lintegral_withDensity_eq_lintegral_mul volume hfn.ennreal_ofReal hφ]
  have hk : Measurable (fun x => ENNReal.ofReal (f (-x)) * φ x) := hfn.ennreal_ofReal.mul hφ
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).lintegral_comp
    hk
  simpa only [neg_neg, Function.comp_def, Pi.mul_apply] using h

theorem conv_realDensityMeasure_reflection {n : ℕ} {f : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hf : IsProbabilityDensity n f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) M) :
    (realDensityMeasure volume f) ∗ (realDensityMeasure volume (fun x => f (-x))) =
      realDensityMeasure volume (differenceDensity f) := by
  have he : (fun x => ENNReal.ofReal (f x)) ⋆ₗ[volume]
      (fun x => ENNReal.ofReal (f (-x))) = fun s => ENNReal.ofReal (differenceDensity f s) := by
    funext s
    rw [lconvolution_def]
    simp only [neg_add, neg_neg, ← sub_eq_add_neg]
    have hi := integrable_difference_slice_of_bounded hf hf.1 hb s
    change (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (f (x - s))) =
      ENNReal.ofReal (∫ x, f x * f (x - s))
    calc
      _ = ∫⁻ x, ENNReal.ofReal (f x * f (x - s)) :=
        lintegral_congr (fun x => (ENNReal.ofReal_mul (hf.2.1 x)).symm)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun x => mul_nonneg (hf.2.1 x) (hf.2.1 (x - s))))).symm
  change volume.withDensity (fun x => ENNReal.ofReal (f x)) ∗
      volume.withDensity (fun x => ENNReal.ofReal (f (-x))) = _
  have hfn : Measurable (fun x => f (-x)) := hf.1.comp measurable_neg
  rw [conv_withDensity_eq_lconvolution (μ := volume) hf.1.ennreal_ofReal hfn.ennreal_ofReal, he]
  rfl

theorem hasLaw_difference_of_logconcave_density {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    {X Y : Ω → (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f)
    (hX : HasLaw X (realDensityMeasure volume f) P)
    (hY : HasLaw Y (realDensityMeasure volume f) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => X ω - Y ω) (realDensityMeasure volume (differenceDensity f)) P := by
  letI : IsProbabilityMeasure (realDensityMeasure volume f) :=
    isProbabilityMeasure_realDensityMeasure hf.2.2.1 hf.2.1 hf.2.2.2
  letI : IsProbabilityMeasure (realDensityMeasure volume (fun x => f (-x))) :=
    isProbabilityMeasure_realDensityMeasure hf.2.2.1.comp_neg (fun x => hf.2.1 (-x))
      (by simpa only [integral_neg_eq_self] using hf.2.2.2)
  have hneg : HasLaw (fun ω => -Y ω) (realDensityMeasure volume (fun x => f (-x))) P :=
    (show HasLaw (fun x => -x) (realDensityMeasure volume (fun x => f (-x)))
      (realDensityMeasure volume f) from
      ⟨measurable_neg.aemeasurable, map_neg_realDensityMeasure hf.1⟩).fun_comp hY
  have hind : IndepFun X (fun ω => -Y ω) P := by
    simpa only [Function.comp_def, id_eq] using hXY.comp measurable_id measurable_neg
  have h := hind.hasLaw_fun_add hX hneg
  obtain ⟨M, hM, hb⟩ := logconcave_probability_density_bounded hf hl
  rw [conv_realDensityMeasure_reflection hf hb] at h
  simpa only [sub_eq_add_neg] using h

theorem sharp_entropic_rogers_shephard_random_vectors {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X Y : Ω → (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f)
    (hX : HasLaw X (realDensityMeasure volume f) P)
    (hY : HasLaw Y (realDensityMeasure volume f) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => X ω - Y ω) (realDensityMeasure volume (differenceDensity f)) P ∧
      Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
      differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤
        (n : ℝ) * Real.log 2 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact ⟨hasLaw_difference_of_logconcave_density hf hl hX hY hXY,
    sharp_entropic_rogers_shephard_density n hn f hf hl⟩

end EntropicRogersShephard
