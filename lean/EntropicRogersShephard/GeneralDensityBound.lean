import EntropicRogersShephard.CompactRestrictions

/-! Pass the sharp compact-restriction bound to the original log-concave density. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem differenceDensity_le_of_domination {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hf : IsProbabilityDensity n f) (hg : IsProbabilityDensity n g)
    (hdom : ∀ x, f x ≤ B * g x) (hb : ∀ x, g x ≤ M) (s : Fin n → ℝ) :
    differenceDensity f s ≤ B ^ 2 * differenceDensity g s := by
  have hgb : ∀ x, g x ∈ Icc (0 : ℝ) M := fun x => ⟨hg.2.1 x, hb x⟩
  have hfb : ∀ x, f x ∈ Icc (0 : ℝ) (B * M) := fun x =>
    ⟨hf.2.1 x, (hdom x).trans (mul_le_mul_of_nonneg_left (hb x) hB)⟩
  have hfi := integrable_difference_slice_of_bounded hf hf.1 hfb s
  have hgi := (integrable_difference_slice_of_bounded hg hg.1 hgb s).const_mul (B ^ 2)
  change (∫ x, f x * f (x - s)) ≤ B ^ 2 * ∫ x, g x * g (x - s)
  rw [← integral_const_mul]
  apply integral_mono hfi hgi
  intro x
  calc
    f x * f (x - s) ≤ (B * g x) * (B * g (x - s)) :=
      mul_le_mul (hdom x) (hdom (x - s)) (hf.2.1 _) (mul_nonneg hB (hg.2.1 _))
    _ = B ^ 2 * (g x * g (x - s)) := by ring

theorem logconcave_probability_density_entropy_increment_bound {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤
      (n : ℝ) * Real.log 2 := by
  obtain ⟨K, hcomp, hconv, hsub, hpos, hp, hdom, hlim⟩ :=
    compact_restrictions_approximation hf hl
  let u (j : ℕ) := powerDensity 1 (K j) f
  have hub : ∀ j, differentialEntropy (differenceDensity (u j)) volume -
      differentialEntropy (u j) volume ≤ (n : ℝ) * Real.log 2 := fun j =>
    (compact_restriction_entropy_finite_and_bound (hcomp j) (hconv j) (hpos j) hf.1 hl (hsub j)).2.2
  obtain ⟨a, C, ha, hC, he⟩ := logconcave_probability_density_exponential_envelope hf hl
  have hue : ∀ j x, u j x ≤ (2 * C) * Real.exp (-a * ‖x‖) := by
    intro j x
    calc
      u j x ≤ 2 * f x := hdom j x
      _ ≤ 2 * (C * Real.exp (-a * ‖x‖)) := mul_le_mul_of_nonneg_left (he x) (by norm_num)
      _ = _ := by ring
  have huL := entropy_tendsto_of_exponential_envelope ha (by positivity : 0 ≤ 2 * C)
    (fun j => (hp j).1) (fun j => (hp j).2.1) hue hlim
  obtain ⟨M, hM, hMb⟩ := logconcave_probability_density_bounded hf hl
  have hgL : ∀ s, Tendsto (fun j => differenceDensity (u j) s) atTop
      (𝓝 (differenceDensity f s)) :=
    differenceDensity_tendsto_of_dominated (by norm_num : (0 : ℝ) ≤ 2) hM.le hf
      (fun j => (hp j).1) (fun j => (hp j).2.1) hdom (fun x => (hMb x).2) hlim
  obtain ⟨D, hD, hge⟩ := differenceDensity_exponential_envelope ha hC.le hf he
  have huge : ∀ j s, differenceDensity (u j) s ≤ (4 * D) * Real.exp (-(a / 2) * ‖s‖) := by
    intro j s
    have hd := differenceDensity_le_of_domination (by norm_num : (0 : ℝ) ≤ 2) hM.le
      (hp j) hf (hdom j) (fun x => (hMb x).2) s
    calc
      differenceDensity (u j) s ≤ 4 * differenceDensity f s := by norm_num at hd; exact hd
      _ ≤ 4 * (D * Real.exp (-(a / 2) * ‖s‖)) :=
        mul_le_mul_of_nonneg_left (hge s) (by norm_num)
      _ = _ := by ring
  have hgEntL := entropy_tendsto_of_exponential_envelope (by positivity : 0 < a / 2)
    (by positivity : 0 ≤ 4 * D)
    (fun j => (isProbabilityDensity_differenceDensity (hp j)).1)
    (fun j => (isProbabilityDensity_differenceDensity (hp j)).2.1)
    huge (Filter.Eventually.of_forall hgL)
  exact le_of_tendsto_of_tendsto' (hgEntL.sub huL) tendsto_const_nhds hub

theorem sharp_entropic_rogers_shephard_density : SharpEntropicRogersShephard := by
  intro n hn f hf hl
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨hi, hg⟩ := logconcave_probability_density_entropies_integrable hf hl
  exact ⟨hi, hg, logconcave_probability_density_entropy_increment_bound hf hl⟩

end EntropicRogersShephard
