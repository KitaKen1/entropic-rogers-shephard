import EntropicRogersShephard.AffineEntropy
import EntropicRogersShephard.AffineLaw
import EntropicRogersShephard.ExponentialSharpness

/-! Every invertible affine image of the exponential-product example attains the bound. -/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

def AttainsSharpEntropicBound (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  IsProbabilityDensity n f ∧ IsLogConcave n f ∧
    Integrable (fun x => Real.negMulLog (f x)) volume ∧
    Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
    differentialEntropy (differenceDensity f) volume - differentialEntropy f volume =
      (n : ℝ) * Real.log 2

theorem sharpness_affine_exponential_product (n : ℕ)
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ) :
    AttainsSharpEntropicBound n (affineDensity A b (productDensity n oneSidedExponential)) := by
  have hf := isProbabilityDensity_exponential_product n
  have hl := isLogConcave_exponential_product n
  have hh := (exponential_product_entropy n).1
  have hg := (exponential_product_difference_entropy n).1
  have hi := (affineDensity_entropy A b hf hh).1
  have hgi : Integrable (fun s => Real.negMulLog
      (differenceDensity (affineDensity A b (productDensity n oneSidedExponential)) s)) volume := by
    rw [differenceDensity_affineDensity]
    exact (affineDensity_entropy A 0 (isProbabilityDensity_differenceDensity hf) hg).1
  refine ⟨isProbabilityDensity_affineDensity A b hf, isLogConcave_affineDensity A b hf.2.1 hl,
    hi, hgi, ?_⟩
  rw [entropy_increment_affineDensity A b hf hh hg, (sharpness_exponential_product n).2.2.2.2]

theorem sharpness_linearEquiv_affine_exponential_product (n : ℕ)
    (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ) :
    AttainsSharpEntropicBound n
      (affineDensity A.toContinuousLinearEquiv b (productDensity n oneSidedExponential)) :=
  sharpness_affine_exponential_product n A.toContinuousLinearEquiv b

theorem hasLaw_affine_exponential_product {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ)
    {X : Ω → (Fin n → ℝ)}
    (hX : HasLaw X (realDensityMeasure volume (productDensity n oneSidedExponential)) P) :
    HasLaw (fun ω => A (X ω) + b)
      (realDensityMeasure volume
        (affineDensity A.toContinuousLinearEquiv b (productDensity n oneSidedExponential))) P := by
  have hf := isProbabilityDensity_exponential_product n
  exact hasLaw_affineDensity A.toContinuousLinearEquiv b hf.1 hf.2.1 hX

end EntropicRogersShephard
