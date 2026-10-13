module
public import FormalConjecturesUtil
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.HasLaw
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant

/-!
# Sharp entropic Rogers–Shephard inequality

Proposed target for https://github.com/google-deepmind/formal-conjectures/issues/7196.
For iid vectors with a log-concave probability density on real n-space, n ≥ 1,
both differential entropies are finite and h(X-X')-h(X) ≤ n log 2.
The exponential-product example and all its invertible affine images attain equality.
Melbourne–Tkocz, arXiv:2005.10930v1, Conjecture 6.1.

This file is a local proposal. It has not been submitted to or accepted by FC.
The mathematical body is checked against lean/Challenge.lean on the proof toolchain.
Compiling the FC metadata against upstream Lean 4.33.1 is not claimed.
-/

@[expose] public section

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

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EntropicRogersShephardFC

@[category research solved, AMS 52 60 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c34631bc744bf626e8225c6c91d5e13c7b8a0b4f/Lean/EntropicRogersShephard/Main.lean"]
theorem density_bound (n : ℕ) (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : ProbabilityDensity n f) (hl : LogConcave n f) :
    Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
      entropy (differenceDensity f) - entropy f ≤ (n : ℝ) * Real.log 2 := by
  sorry

@[category research solved, AMS 52 60 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c34631bc744bf626e8225c6c91d5e13c7b8a0b4f/Lean/EntropicRogersShephard/Main.lean"]
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

@[category research solved, AMS 52 60 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c34631bc744bf626e8225c6c91d5e13c7b8a0b4f/Lean/EntropicRogersShephard/Main.lean"]
theorem affine_density_law (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (hf : ProbabilityDensity n f) :
    (densityMeasure f).map (fun x => A x + b) = densityMeasure (affineImage A b f) := by
  sorry

@[category research solved, AMS 52 60 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c34631bc744bf626e8225c6c91d5e13c7b8a0b4f/Lean/EntropicRogersShephard/Main.lean"]
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

@[category research solved, AMS 52 60 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c34631bc744bf626e8225c6c91d5e13c7b8a0b4f/Lean/EntropicRogersShephard/Main.lean"]
theorem constant_optimal (n : ℕ) (C : ℝ)
    (hC : ∀ f : (Fin n → ℝ) → ℝ, ProbabilityDensity n f → LogConcave n f →
      entropy (differenceDensity f) - entropy f ≤ C) :
    (n : ℝ) * Real.log 2 ≤ C := by
  sorry

end EntropicRogersShephardFC
