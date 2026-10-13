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

theorem entropic_rogers_shephard {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (X Y : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ProbabilityDensity n f) (hl : LogConcave n f)
    (hX : HasLaw X (volume.withDensity (fun x => ENNReal.ofReal (f x))) P)
    (hY : HasLaw Y (volume.withDensity (fun x => ENNReal.ofReal (f x))) P)
    (hXY : IndepFun X Y P) :
    let g : (Fin n → ℝ) → ℝ := fun s => ∫ x, f x * f (x - s)
    HasLaw (fun ω => X ω - Y ω) (volume.withDensity (fun s => ENNReal.ofReal (g s))) P ∧
      Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (g s)) volume ∧
      (∫ s, Real.negMulLog (g s)) - (∫ x, Real.negMulLog (f x)) ≤ (n : ℝ) * Real.log 2 := by
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
