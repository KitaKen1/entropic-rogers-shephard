import EntropicRogersShephard
import EntropicRogersShephard.ConvexApproximation
import Mathlib.Analysis.Convex.Continuous

/-! The native rpow definition gives a continuous logarithm on the interior of the positive set. -/

open MeasureTheory Set Real

namespace EntropicRogersShephard

theorem convex_positiveSet_of_isLogConcave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) : Convex ℝ {x | 0 < f x} := by
  intro x hx y hy a b ha hb hab
  exact (mul_pos (Real.rpow_pos_of_pos hx a) (Real.rpow_pos_of_pos hy b)).trans_le
    (hf x y a b ha hb hab)

theorem concaveOn_log_of_isLogConcave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) := by
  refine ⟨convex_positiveSet_of_isLogConcave hf, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := (convex_positiveSet_of_isLogConcave hf) hx hy ha hb hab
  apply (Real.le_log_iff_exp_le hz).mpr
  have hi : (f x) ^ a * (f y) ^ b ≤ f (a • x + b • y) := hf x y a b ha hb hab
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy] at hi
  simpa only [smul_eq_mul, Real.exp_add, mul_comm] using hi

theorem continuousOn_log_positiveInterior {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) :
    ContinuousOn (fun x => Real.log (f x)) (interior {x | 0 < f x}) :=
  (concaveOn_log_of_isLogConcave hf).continuousOn_interior

theorem continuousOn_positiveInterior {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) : ContinuousOn f (interior {x | 0 < f x}) := by
  apply (Real.continuous_exp.comp_continuousOn (continuousOn_log_positiveInterior hf)).congr
  intro x hx
  have hp : 0 < f x := interior_subset (s := {x | 0 < f x}) hx
  exact (Real.exp_log hp).symm

theorem positiveInterior_ae_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) : (interior {x | 0 < f x}) =ᵐ[volume] {x | 0 < f x} :=
  interior_ae_eq_of_null_frontier ((convex_positiveSet_of_isLogConcave hf).addHaar_frontier volume)

theorem positiveInterior_nonempty {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    (interior {x | 0 < f x}).Nonempty := by
  by_contra h
  have he := Set.not_nonempty_iff_eq_empty.mp h
  have hz : f =ᵐ[volume] (fun _ => 0) := by
    filter_upwards [positiveInterior_ae_eq hl] with x hx
    have hn : ¬ 0 < f x := by
      intro hp
      exact Set.notMem_empty x (he ▸ hx.mpr hp)
    exact le_antisymm (not_lt.mp hn) (hf.2.1 x)
  have hi : (∫ x, f x) = 0 := by rw [integral_congr_ae hz, integral_zero]
  linarith [hf.2.2.2]

theorem compact_positiveInterior_bounds {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {K : Set (Fin n → ℝ)} (hl : IsLogConcave n f) (hK : IsCompact K)
    (hne : K.Nonempty) (hsub : K ⊆ interior {x | 0 < f x}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, f x ∈ Icc c C := by
  have hc := (continuousOn_positiveInterior hl).mono hsub
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hc
  have hxpos : 0 < f x := interior_subset (s := {x | 0 < f x}) (hsub hx)
  have hypos : 0 < f y := interior_subset (s := {x | 0 < f x}) (hsub hy)
  exact ⟨f x, f y, hxpos, hypos,
    fun z hz => ⟨hmin hz, hmax hz⟩⟩

end EntropicRogersShephard
