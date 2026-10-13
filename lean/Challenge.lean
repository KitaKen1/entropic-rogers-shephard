import FCTargetDefinitions

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EntropicRogersShephardFC

theorem density_bound (n : ℕ) (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : ProbabilityDensity n f) (hl : LogConcave n f) :
    Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
      entropy (differenceDensity f) - entropy f ≤ (n : ℝ) * Real.log 2 := by
  sorry

theorem random_vector_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (X Y : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ProbabilityDensity n f) (hl : LogConcave n f)
    (hX : HasLaw X (densityMeasure f) P) (hY : HasLaw Y (densityMeasure f) P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω => X ω - Y ω) (densityMeasure (differenceDensity f)) P ∧
      Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
      entropy (differenceDensity f) - entropy f ≤ (n : ℝ) * Real.log 2 := by
  sorry

theorem affine_density_law (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (hf : ProbabilityDensity n f) :
    (densityMeasure f).map (fun x => A x + b) = densityMeasure (affineImage A b f) := by
  sorry

theorem affine_exponential_equality (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) :
    ProbabilityDensity n (affineImage A b (exponentialProduct n)) ∧
      LogConcave n (affineImage A b (exponentialProduct n)) ∧
      Integrable (fun x => Real.negMulLog (affineImage A b (exponentialProduct n) x)) volume ∧
      Integrable (fun s => Real.negMulLog
        (differenceDensity (affineImage A b (exponentialProduct n)) s)) volume ∧
      entropy (differenceDensity (affineImage A b (exponentialProduct n))) -
        entropy (affineImage A b (exponentialProduct n)) = (n : ℝ) * Real.log 2 := by
  sorry

theorem constant_optimal (n : ℕ) (C : ℝ)
    (hC : ∀ f : (Fin n → ℝ) → ℝ, ProbabilityDensity n f → LogConcave n f →
      entropy (differenceDensity f) - entropy f ≤ C) :
    (n : ℝ) * Real.log 2 ≤ C := by
  sorry

end EntropicRogersShephardFC
