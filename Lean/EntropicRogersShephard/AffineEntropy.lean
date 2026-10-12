import EntropicRogersShephard.AffineDensity

/-! The same determinant correction occurs in both differential entropies. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem affineDensity_entropy {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f)
    (hh : Integrable (fun x => Real.negMulLog (f x)) volume) :
    Integrable (fun x => Real.negMulLog (affineDensity A b f x)) volume ∧
      differentialEntropy (affineDensity A b f) volume =
        differentialEntropy f volume - Real.log (affineJacobian A) := by
  let J := affineJacobian A
  have hJ : 0 < J := affineJacobian_pos A
  have he : (fun x => Real.negMulLog (affineDensity A b f x)) =
      (fun x => J * Real.negMulLog (f (A.symm (x - b))) +
        Real.negMulLog J * f (A.symm (x - b))) := by
    funext x
    change Real.negMulLog (J * f (A.symm (x - b))) = _
    rw [Real.negMulLog_mul]
    ring
  have hi1 : Integrable (fun x => J * Real.negMulLog (f (A.symm (x - b)))) volume :=
    (integrable_affine_inverse A b hh).const_mul J
  have hi2 : Integrable (fun x => Real.negMulLog J * f (A.symm (x - b))) volume :=
    (integrable_affine_inverse A b hf.2.2.1).const_mul (Real.negMulLog J)
  have hi : Integrable (fun x => Real.negMulLog (affineDensity A b f x)) volume := by
    rw [he]
    exact hi1.add hi2
  refine ⟨hi, ?_⟩
  change (∫ x, Real.negMulLog (affineDensity A b f x)) = _
  rw [he, integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_affine_inverse A b (fun x => Real.negMulLog (f x)),
    integral_affine_inverse A b f, hf.2.2.2]
  change J * (J⁻¹ * differentialEntropy f volume) + Real.negMulLog J * (J⁻¹ * 1) =
    differentialEntropy f volume - Real.log J
  simp only [Real.negMulLog_def]
  field_simp [hJ.ne']
  ring

theorem entropy_increment_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f)
    (hh : Integrable (fun x => Real.negMulLog (f x)) volume)
    (hg : Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume) :
    differentialEntropy (differenceDensity (affineDensity A b f)) volume -
      differentialEntropy (affineDensity A b f) volume =
      differentialEntropy (differenceDensity f) volume - differentialEntropy f volume := by
  have hi := (affineDensity_entropy A b hf hh).2
  have hd := (affineDensity_entropy A 0 (isProbabilityDensity_differenceDensity hf) hg).2
  rw [differenceDensity_affineDensity, hi, hd]
  ring

theorem logconcave_affine_entropy_increment {n : ℕ} [NeZero n]
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    differentialEntropy (differenceDensity (affineDensity A b f)) volume -
      differentialEntropy (affineDensity A b f) volume =
      differentialEntropy (differenceDensity f) volume - differentialEntropy f volume := by
  obtain ⟨hh, hg⟩ := logconcave_probability_density_entropies_integrable hf hl
  exact entropy_increment_affineDensity A b hf hh hg

end EntropicRogersShephard
