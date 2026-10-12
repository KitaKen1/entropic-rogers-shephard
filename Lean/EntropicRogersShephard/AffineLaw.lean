import EntropicRogersShephard.AffineDensity

/-! The transported density is the actual affine pushforward law. -/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem map_affine_realDensityMeasure {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    (realDensityMeasure volume f).map (fun x => A x + b) =
      realDensityMeasure volume (affineDensity A b f) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have ha : Measurable (fun x => A x + b) := by fun_prop
  have hφa : Measurable (fun x => φ (A x + b)) := hφ.comp ha
  have hfa : Measurable (affineDensity A b f) := measurable_affineDensity A b hf
  simp only [realDensityMeasure]
  rw [lintegral_map hφ ha,
    lintegral_withDensity_eq_lintegral_mul volume hf.ennreal_ofReal hφa,
    lintegral_withDensity_eq_lintegral_mul volume hfa.ennreal_ofReal hφ]
  change (∫⁻ x, ENNReal.ofReal (f x) * φ (A x + b)) =
    ∫⁻ x, ENNReal.ofReal (affineDensity A b f x) * φ x
  let q (y : Fin n → ℝ) := ENNReal.ofReal (f y) * φ (A y + b)
  have hp (x : Fin n → ℝ) : ENNReal.ofReal (affineDensity A b f x) * φ x =
      ENNReal.ofReal (affineJacobian A) * q (A.symm (x - b)) := by
    dsimp [affineDensity, q]
    rw [ENNReal.ofReal_mul (affineJacobian_pos A).le, A.apply_symm_apply, sub_add_cancel]
    exact mul_assoc _ _ _
  rw [lintegral_congr hp,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_affine_inverse A b q,
    ← mul_assoc, ← ENNReal.ofReal_mul (affineJacobian_pos A).le,
    mul_inv_cancel₀ (affineJacobian_pos A).ne', ENNReal.ofReal_one, one_mul]

theorem hasLaw_affineDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ)
    {X : Ω → (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) (hX : HasLaw X (realDensityMeasure volume f) P) :
    HasLaw (fun ω => A (X ω) + b) (realDensityMeasure volume (affineDensity A b f)) P := by
  have ha : HasLaw (fun x => A x + b) (realDensityMeasure volume (affineDensity A b f))
      (realDensityMeasure volume f) :=
    ⟨(by fun_prop : Measurable (fun x => A x + b)).aemeasurable,
      map_affine_realDensityMeasure A b hf hn⟩
  exact ha.fun_comp hX

end EntropicRogersShephard
