import EntropicRogersShephard.ExponentialExample

/-! The explicit exponential-product equality example in every dimension. -/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem differenceDensity_productDensity (n : ℕ) (f : ℝ → ℝ) :
    differenceDensity (productDensity n f) =
      productDensity n (fun s => ∫ t, f t * f (t - s)) := by
  funext s
  change (∫ x : Fin n → ℝ, (∏ i, f (x i)) * (∏ i, f ((x - s) i))) = _
  simp only [Pi.sub_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod (fun i t => f t * f (t - s i))

theorem isProbabilityDensity_exponential_product (n : ℕ) :
    IsProbabilityDensity n (productDensity n oneSidedExponential) :=
  isProbabilityDensity_productDensity n measurable_oneSidedExponential
    oneSidedExponential_nonneg integrable_oneSidedExponential integral_oneSidedExponential

theorem isLogConcave_exponential_product (n : ℕ) :
    IsLogConcave n (productDensity n oneSidedExponential) :=
  isLogConcave_productDensity n oneSidedExponential_nonneg scalarLogConcave_oneSidedExponential

theorem differenceDensity_exponential_product (n : ℕ) :
    differenceDensity (productDensity n oneSidedExponential) = productDensity n unitLaplace := by
  rw [differenceDensity_productDensity]
  simp_rw [integral_oneSidedExponential_difference]

theorem exponential_product_entropy (n : ℕ) :
    Integrable (fun x => Real.negMulLog (productDensity n oneSidedExponential x)) volume ∧
      differentialEntropy (productDensity n oneSidedExponential) volume = (n : ℝ) := by
  have h := productDensity_entropy n integrable_oneSidedExponential integral_oneSidedExponential
    oneSidedExponential_entropy.1
  simpa only [oneSidedExponential_entropy.2, mul_one] using h

theorem exponential_product_difference_entropy (n : ℕ) :
    Integrable (fun s => Real.negMulLog (differenceDensity (productDensity n oneSidedExponential) s)) volume ∧
      differentialEntropy (differenceDensity (productDensity n oneSidedExponential)) volume =
        (n : ℝ) * (1 + Real.log 2) := by
  rw [differenceDensity_exponential_product]
  have h := productDensity_entropy n integrable_unitLaplace integral_unitLaplace unitLaplace_entropy.1
  simpa only [unitLaplace_entropy.2] using h

theorem sharpness_exponential_product (n : ℕ) :
    IsProbabilityDensity n (productDensity n oneSidedExponential) ∧
      IsLogConcave n (productDensity n oneSidedExponential) ∧
      Integrable (fun x => Real.negMulLog (productDensity n oneSidedExponential x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity (productDensity n oneSidedExponential) s)) volume ∧
      differentialEntropy (differenceDensity (productDensity n oneSidedExponential)) volume -
        differentialEntropy (productDensity n oneSidedExponential) volume = (n : ℝ) * Real.log 2 := by
  refine ⟨isProbabilityDensity_exponential_product n, isLogConcave_exponential_product n,
    (exponential_product_entropy n).1, (exponential_product_difference_entropy n).1, ?_⟩
  rw [(exponential_product_entropy n).2, (exponential_product_difference_entropy n).2]
  ring

theorem entropy_increment_constant_optimal (n : ℕ) {C : ℝ}
    (hC : ∀ f : (Fin n → ℝ) → ℝ, IsProbabilityDensity n f → IsLogConcave n f →
      differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤ C) :
    (n : ℝ) * Real.log 2 ≤ C := by
  have h := hC (productDensity n oneSidedExponential)
    (isProbabilityDensity_exponential_product n) (isLogConcave_exponential_product n)
  rw [(sharpness_exponential_product n).2.2.2.2] at h
  exact h

end EntropicRogersShephard
