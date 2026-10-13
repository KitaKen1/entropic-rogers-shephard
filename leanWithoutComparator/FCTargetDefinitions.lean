import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.HasLaw
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-! Standalone definitions for the proposed target of FC issue #7196.
These depend only on Mathlib, never on the submitted proof. No definition holes.
Euclidean n-space uses coordinates `Fin n → ℝ` with Lebesgue measure. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EntropicRogersShephardFC

def ProbabilityDensity (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ (∫ x, f x) = 1

/-- Multiplicative log-concavity, including zeros and the endpoint weights. -/
def LogConcave (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    Real.rpow (f x) a * Real.rpow (f y) b ≤ f (a • x + b • y)

noncomputable def differenceDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (s : Fin n → ℝ) : ℝ := ∫ x, f x * f (x - s)

/-- Differential Shannon entropy, using natural logarithms and `0 log 0 = 0`. -/
noncomputable def entropy {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, Real.negMulLog (f x)

noncomputable def densityMeasure {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Measure (Fin n → ℝ) := volume.withDensity (fun x => ENNReal.ofReal (f x))

noncomputable def exponentialProduct (n : ℕ) : (Fin n → ℝ) → ℝ :=
  fun x => ∏ i, (Set.Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) (x i)

/-- The density of `A X + b`: absolute determinant of the inverse times `f(A⁻¹(x-b))`. -/
noncomputable def affineImage {n : ℕ} (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => |LinearMap.det (A.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| *
    f (A.symm (x - b))

end EntropicRogersShephardFC
