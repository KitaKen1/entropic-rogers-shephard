import EntropicRogersShephard.ConvexVolume
import EntropicRogersShephard.ConvexExhaustion

/-! Compact convex exhaustion, ignoring the null boundary of a convex support. -/

open MeasureTheory Set
open scoped ENNReal

namespace EntropicRogersShephard

/-- The compact pieces cover a convex support almost everywhere. Every piece lies
inside the interior, where a finite concave logarithm is continuous. -/
theorem compact_convex_exhaustion {n : ℕ} {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) :
    ∃ K : ℕ → Set (Fin n → ℝ), Monotone K ∧ (∀ j, IsCompact (K j)) ∧
      (∀ j, Convex ℝ (K j)) ∧ (∀ j, K j ⊆ interior C) ∧
      (⋃ j, K j) = interior C ∧ (⋃ j, K j) =ᵐ[volume] C := by
  obtain ⟨U, hmono, hopen, hconv, hcompact, hsub, hcover⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq isOpen_interior hC.interior
  have hclosedCover : (⋃ j, closure (U j)) = interior C := by
    refine subset_antisymm (iUnion_subset hsub) ?_
    rw [← hcover]
    exact iUnion_mono fun j => subset_closure
  refine ⟨fun j => closure (U j), fun i j hij => closure_mono (hmono hij), hcompact,
    fun j => (hconv j).closure, hsub, hclosedCover, ?_⟩
  rw [hclosedCover]
  exact interior_ae_eq_of_null_frontier (hC.addHaar_frontier volume)

/-- A convex set of finite volume that contains a ball is bounded. This is the
geometric step needed to bound a positive density superlevel set. -/
theorem convex_isBounded_of_volume_ne_top {n : ℕ} [NeZero n]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hfin : volume C ≠ ∞)
    {x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ C) :
    Bornology.IsBounded C := by
  let N := Module.finrank ℝ (Fin n → ℝ)
  let v := (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal
  have hv : 0 < v := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Fin n → ℝ) (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_ne_top
  have hden : 0 < r ^ (N - 1) * v := mul_pos (pow_pos hr _) hv
  refine (Metric.isBounded_iff_subset_closedBall x).mpr
    ⟨2 ^ (N + 1) * (volume C).toReal / (r ^ (N - 1) * v), ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  apply (le_div_iff₀ hden).mpr
  have h := convex_ball_point_volume_lower (μ := volume) hC hr hball hy
  have htop : (2 : ℝ≥0∞) ^ (N + 1) * volume C ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hfin
  have ht := ENNReal.toReal_mono htop h
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg dist_nonneg (pow_nonneg hr.le _)),
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at ht
  change dist y x * (r ^ (N - 1) * v) ≤ _
  convert ht using 1 <;> ring

end EntropicRogersShephard
