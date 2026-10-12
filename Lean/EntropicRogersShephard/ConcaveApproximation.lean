import EntropicRogersShephard.FiniteSupportLimit
import EntropicRogersShephard.FiberExtension
import EntropicRogersShephard.CompactConvergence

/-! Positive concave-power approximations of a bounded convex potential on a fixed support. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

noncomputable def concavePowerSize {n : ℕ} (M : ℕ) (V : (Fin n → ℝ) → ℝ) (j : ℕ) :
    (Fin n → ℝ) → ℝ := fun x => 1 - V x / ((j + M : ℕ) : ℝ)

noncomputable def compactExponentialDensity {n : ℕ} (K : Set (Fin n → ℝ))
    (V : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  powerDensity 1 K (fun x => Real.exp (-V x))

noncomputable def normalizedPowerApproximation {n : ℕ} (M : ℕ) (K : Set (Fin n → ℝ))
    (V : (Fin n → ℝ) → ℝ) (j : ℕ) : (Fin n → ℝ) → ℝ :=
  powerDensity (j + M) K (concavePowerSize M V j)

theorem measurable_concavePowerSize {n : ℕ} (M j : ℕ) {V : (Fin n → ℝ) → ℝ}
    (hm : Measurable V) : Measurable (concavePowerSize M V j) :=
  measurable_const.sub (hm.div_const _)

theorem continuousOn_concavePowerSize {n : ℕ} (M j : ℕ) {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} (hc : ContinuousOn V K) : ContinuousOn (concavePowerSize M V j) K :=
  continuousOn_const.sub (hc.div_const _)

theorem concaveOn_concavePowerSize {n : ℕ} (M j : ℕ) {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} (hV : ConvexOn ℝ K V) (hM : 0 < M) :
    ConcaveOn ℝ K (concavePowerSize M V j) := by
  have hd : 0 < ((j + M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j + M)
  refine ⟨hV.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmix : V (a • x + b • y) ≤ a * V x + b * V y := by
    simpa only [smul_eq_mul] using hV.2 hx hy ha hb hab
  change a * (1 - V x / ((j + M : ℕ) : ℝ)) + b * (1 - V y / ((j + M : ℕ) : ℝ)) ≤
    1 - V (a • x + b • y) / ((j + M : ℕ) : ℝ)
  calc
    _ = (a + b) - (a * V x + b * V y) / ((j + M : ℕ) : ℝ) := by ring
    _ = 1 - (a * V x + b * V y) / ((j + M : ℕ) : ℝ) := by rw [hab]
    _ ≤ _ := sub_le_sub_left (div_le_div_of_nonneg_right hmix hd.le) 1

theorem concavePowerSize_mem_Icc {n : ℕ} {M j : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) {x : Fin n → ℝ} (hx : x ∈ K) :
    concavePowerSize M V j x ∈ Icc (1 / 2 : ℝ) 1 := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hd : 0 < ((j + M : ℕ) : ℝ) := by push_cast; nlinarith
  have hv : V x / ((j + M : ℕ) : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    nlinarith [(hb x hx).2]
  exact ⟨by dsimp [concavePowerSize]; linarith,
    sub_le_self _ (div_nonneg (hb x hx).1 hd.le)⟩

theorem exponential_size_bounds {n : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R)
    {x : Fin n → ℝ} (hx : x ∈ K) : Real.exp (-V x) ∈ Icc (Real.exp (-R)) 1 := by
  refine ⟨Real.exp_le_exp.mpr (neg_le_neg (hb x hx).2), ?_⟩
  calc
    Real.exp (-V x) ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (hb x hx).1)
    _ = 1 := Real.exp_zero

theorem compact_exponential_mass_pos {n : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hpos : volume K ≠ 0) (hm : Measurable V) (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    0 < powerMass 1 K (fun x => Real.exp (-V x)) :=
  powerMass_pos hK hfin hpos hm.neg.exp (Real.exp_pos _) (by norm_num)
    (fun _ hx => exponential_size_bounds hb hx)

theorem isProbabilityDensity_compactExponentialDensity {n : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hpos : volume K ≠ 0) (hm : Measurable V) (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    IsProbabilityDensity n (compactExponentialDensity K V) :=
  isProbabilityDensity_powerDensity hK hfin hpos hm.neg.exp (Real.exp_pos _) (by norm_num)
    (fun _ hx => exponential_size_bounds hb hx)

theorem concave_power_weight_tendsto {n : ℕ} (M : ℕ) (K : Set (Fin n → ℝ))
    (V : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Tendsto (fun j => powerWeight (j + M) K (concavePowerSize M V j) x) atTop
      (𝓝 (powerWeight 1 K (fun x => Real.exp (-V x)) x)) := by
  by_cases hx : x ∈ K
  · simp only [powerWeight, Set.indicator_of_mem hx, concavePowerSize, pow_one]
    change Tendsto (powerApproximation M (V x)) atTop (𝓝 (Real.exp (-V x)))
    exact powerApproximation_tendsto M (V x)
  · simpa only [powerWeight, Set.indicator_of_notMem hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem concave_power_mass_tendsto {n : ℕ} {M : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hm : Measurable V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    Tendsto (fun j => powerMass (j + M) K (concavePowerSize M V j)) atTop
      (𝓝 (powerMass 1 K (fun x => Real.exp (-V x)))) := by
  apply integral_tendsto_of_bounded_support hK hfin
    (fun j => measurable_powerWeight hK (measurable_concavePowerSize M j hm)) (C := 1)
  · intro j x
    have hs : ∀ y ∈ K, concavePowerSize M V j y ∈ Icc (0 : ℝ) 1 :=
      fun y hy => ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans (concavePowerSize_mem_Icc hR hM hb hy).1,
        (concavePowerSize_mem_Icc hR hM hb hy).2⟩
    exact ⟨powerWeight_nonneg (fun y hy => (hs y hy).1) x,
      by simpa only [one_pow] using powerWeight_le (by norm_num : (0 : ℝ) ≤ 1) hs x⟩
  · exact fun _ _ hx => powerWeight_eq_zero_of_not_mem hx
  · exact concave_power_weight_tendsto M K V

theorem concave_power_mass_pos {n : ℕ} {M j : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hpos : volume K ≠ 0) (hm : Measurable V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    0 < powerMass (j + M) K (concavePowerSize M V j) :=
  powerMass_pos hK hfin hpos (measurable_concavePowerSize M j hm) (by norm_num) (by norm_num)
    (fun _ hx => concavePowerSize_mem_Icc hR hM hb hx)

theorem isProbabilityDensity_normalizedPowerApproximation {n : ℕ} {M j : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hpos : volume K ≠ 0) (hm : Measurable V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    IsProbabilityDensity n (normalizedPowerApproximation M K V j) :=
  isProbabilityDensity_powerDensity hK hfin hpos (measurable_concavePowerSize M j hm)
    (by norm_num) (by norm_num) (fun _ hx => concavePowerSize_mem_Icc hR hM hb hx)

theorem normalizedPowerApproximation_tendsto {n : ℕ} {M : ℕ} {K : Set (Fin n → ℝ)}
    {V : (Fin n → ℝ) → ℝ} {R : ℝ} (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (hpos : volume K ≠ 0) (hm : Measurable V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) (x : Fin n → ℝ) :
    Tendsto (fun j => normalizedPowerApproximation M K V j x) atTop
      (𝓝 (compactExponentialDensity K V x)) := by
  exact (concave_power_weight_tendsto M K V x).div (concave_power_mass_tendsto hK hfin hm hR hM hb)
    (compact_exponential_mass_pos hK hfin hpos hm hb).ne'

theorem normalizedPowerApproximation_entropy_increment_bound {n : ℕ} {M j : ℕ}
    {K : Set (Fin n → ℝ)} {V : (Fin n → ℝ) → ℝ} {R : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hm : Measurable V) (hc : ContinuousOn V K)
    (hV : ConvexOn ℝ K V) (hR : 0 ≤ R) (hM : 2 * R < (M : ℝ))
    (hb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) R) :
    differentialEntropy (differenceDensity (normalizedPowerApproximation M K V j)) volume -
      differentialEntropy (normalizedPowerApproximation M K V j) volume ≤ F (n + (j + M)) - F (j + M) := by
  have hMp : 0 < (M : ℝ) := by nlinarith
  have hMn : 0 < M := by exact_mod_cast hMp
  letI : NeZero (j + M) := ⟨by omega⟩
  letI : NeZero (n + (j + M)) := ⟨by omega⟩
  exact power_density_entropy_increment_bound hK hpos (measurable_concavePowerSize M j hm)
    (continuousOn_concavePowerSize M j hc) (concaveOn_concavePowerSize M j hV hMn)
    (by norm_num) (by norm_num) (fun _ hx => concavePowerSize_mem_Icc hR hM hb hx)

end EntropicRogersShephard
