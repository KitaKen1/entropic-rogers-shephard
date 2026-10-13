import EntropicRogersShephard.LogConcavity
import EntropicRogersShephard.Density
import Mathlib.Analysis.Convex.Topology

/-! Positive superlevels are bounded; midpoint continuity then bounds the density globally. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem convex_positive_superlevel {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcave n f) {t : ℝ} (ht : 0 < t) : Convex ℝ {x | t ≤ f x} := by
  intro x hx y hy a b ha hb hab
  have hLC : (f x) ^ a * (f y) ^ b ≤ f (a • x + b • y) := hf x y a b ha hb hab
  calc
    t = t ^ a * t ^ b := by rw [← Real.rpow_add ht, hab, Real.rpow_one]
    _ ≤ (f x) ^ a * (f y) ^ b := mul_le_mul
      (Real.rpow_le_rpow ht.le hx ha) (Real.rpow_le_rpow ht.le hy hb)
      (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (ht.le.trans hx) _)
    _ ≤ f (a • x + b • y) := hLC

theorem exists_density_anchor_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    ∃ x ∈ interior {x | 0 < f x}, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r, f x / 2 ≤ f y := by
  obtain ⟨x, hx⟩ := positiveInterior_nonempty hf hl
  have hfx : 0 < f x := interior_subset (s := {x | 0 < f x}) hx
  have hc : ContinuousAt f x := (continuousOn_positiveInterior hl).continuousAt (isOpen_interior.mem_nhds hx)
  have hhalf : f x / 2 < f x := by linarith
  have hn : {y | f x / 2 < f y} ∩ interior {x | 0 < f x} ∈ 𝓝 x :=
    inter_mem (hc.tendsto.eventually (eventually_gt_nhds hhalf)) (isOpen_interior.mem_nhds hx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hn
  exact ⟨x, hx, r, hr, fun y hy => (hball hy).1.le⟩

theorem logconcave_superlevel_isBounded {n : ℕ} [NeZero n] {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) {t : ℝ} (ht : 0 < t)
    {x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ {y | t ≤ f y}) :
    Bornology.IsBounded {y | t ≤ f y} :=
  convex_isBounded_of_volume_ne_top (convex_positive_superlevel hl ht)
    (hf.2.2.1.measure_ge_lt_top ht).ne hr hball

theorem logconcave_probability_density_bounded {n : ℕ} [NeZero n] {f : (Fin n → ℝ) → ℝ}
    (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    ∃ M : ℝ, 0 < M ∧ ∀ y, f y ∈ Icc (0 : ℝ) M := by
  obtain ⟨x, hx, r, hr, hball⟩ := exists_density_anchor_ball hf hl
  have hfx : 0 < f x := interior_subset (s := {x | 0 < f x}) hx
  let t := f x / 2
  have ht : 0 < t := by dsimp [t]; positivity
  let A := {y | t ≤ f y}
  have hA : Bornology.IsBounded A := logconcave_superlevel_isBounded hf hl ht hr hball
  have hAS : A ⊆ {y | 0 < f y} := fun _ hy => ht.trans_le hy
  let F := fun y : Fin n → ℝ => (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  let T := F '' closure A
  have hT : IsCompact T := hA.isCompact_closure.image (by fun_prop : Continuous F)
  have hTS : T ⊆ interior {y | 0 < f y} := by
    rintro z ⟨y, hy, rfl⟩
    exact (convex_positiveSet_of_isLogConcave hl).combo_interior_closure_mem_interior hx
      (closure_mono hAS hy) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB⟩ := hT.bddAbove_image ((continuousOn_positiveInterior hl).mono hTS)
  refine ⟨max t (B ^ 2 / f x), ht.trans_le (le_max_left _ _), ?_⟩
  intro y
  refine ⟨hf.2.1 y, ?_⟩
  by_cases hy : y ∈ A
  · have hFy : F y ∈ T := ⟨y, subset_closure hy, rfl⟩
    have hupper : f (F y) ≤ B := hB ⟨F y, hFy, rfl⟩
    have hLC : (f x) ^ (1 / 2 : ℝ) * (f y) ^ (1 / 2 : ℝ) ≤ f (F y) :=
      hl x y (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    have hsqrt : Real.sqrt (f x) * Real.sqrt (f y) ≤ B := by
      have h := hLC.trans hupper
      simpa only [← Real.sqrt_eq_rpow] using h
    have hsq := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hsqrt 2
    rw [mul_pow, Real.sq_sqrt hfx.le, Real.sq_sqrt (hf.2.1 y)] at hsq
    exact ((le_div_iff₀ hfx).mpr (by simpa only [mul_comm] using hsq)).trans (le_max_right _ _)
  · have hy' : f y < t := lt_of_not_ge hy
    exact hy'.le.trans (le_max_left _ _)

end EntropicRogersShephard
