import EntropicRogersShephard.AffineSharpness
import EntropicRogersShephard.MonotoneTilt

/-! Final density, probability-law, affine equality and optimality statements. -/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

universe u

def RandomVectorEntropicRogersShephard : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
    ∀ (n : ℕ), 0 < n → ∀ (X Y : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
      IsProbabilityDensity n f → IsLogConcave n f →
      HasLaw X (realDensityMeasure volume f) P → HasLaw Y (realDensityMeasure volume f) P →
      IndepFun X Y P →
      HasLaw (fun ω => X ω - Y ω) (realDensityMeasure volume (differenceDensity f)) P ∧
        Integrable (fun x => Real.negMulLog (f x)) volume ∧
        Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
        differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤
          (n : ℝ) * Real.log 2

def AffineDensityPushforward : Prop :=
  ∀ (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ), IsProbabilityDensity n f →
    (realDensityMeasure volume f).map (fun x => A x + b) =
      realDensityMeasure volume (affineDensity A.toContinuousLinearEquiv b f)

def AffineExponentialEqualityFamily : Prop :=
  ∀ (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ),
    AttainsSharpEntropicBound n
      (affineDensity A.toContinuousLinearEquiv b (productDensity n oneSidedExponential))

def EntropicBoundOptimal : Prop :=
  ∀ (n : ℕ) (C : ℝ),
    (∀ f : (Fin n → ℝ) → ℝ, IsProbabilityDensity n f → IsLogConcave n f →
      differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤ C) →
      (n : ℝ) * Real.log 2 ≤ C

def CompleteSharpEntropicRogersShephard : Prop :=
  SharpEntropicRogersShephard ∧ RandomVectorEntropicRogersShephard.{u} ∧
    AffineDensityPushforward ∧ AffineExponentialEqualityFamily ∧ EntropicBoundOptimal

theorem complete_sharp_entropic_rogers_shephard : CompleteSharpEntropicRogersShephard.{u} := by
  refine ⟨sharp_entropic_rogers_shephard_density, ?_, ?_, ?_, ?_⟩
  · intro Ω mΩ P hP n hn X Y f hf hl hX hY hXY
    exact sharp_entropic_rogers_shephard_random_vectors hn hf hl hX hY hXY
  · intro n A b f hf
    exact map_affine_realDensityMeasure A.toContinuousLinearEquiv b hf.1 hf.2.1
  · intro n A b
    exact sharpness_linearEquiv_affine_exponential_product n A b
  · intro n C hC
    exact entropy_increment_constant_optimal n hC

end EntropicRogersShephard
