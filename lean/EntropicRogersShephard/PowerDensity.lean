import EntropicRogersShephard.Density

/-! Normalized powers on a finite support and their entropy identity. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def powerWeight {n : ℕ} (m : ℕ) (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  K.indicator (fun x => ρ x ^ m)

noncomputable def powerMass {n : ℕ} (m : ℕ) (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : ℝ := ∫ x, powerWeight m K ρ x

noncomputable def powerDensity {n : ℕ} (m : ℕ) (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => powerWeight m K ρ x / powerMass m K ρ

theorem measurable_powerWeight {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    Measurable (powerWeight m K ρ) := (hρ.pow_const m).indicator hK

theorem powerWeight_nonneg {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hρ : ∀ x ∈ K, 0 ≤ ρ x) (x : Fin n → ℝ) :
    0 ≤ powerWeight m K ρ x :=
  Set.indicator_nonneg (fun x hx => pow_nonneg (hρ x hx) m) x

theorem powerWeight_eq_zero_of_not_mem {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∉ K) :
    powerWeight m K ρ x = 0 := Set.indicator_of_notMem hx _

theorem powerWeight_le {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hρ : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C) (x : Fin n → ℝ) :
    powerWeight m K ρ x ≤ C ^ m := by
  by_cases hx : x ∈ K
  · exact (Set.indicator_of_mem hx _).trans_le (pow_le_pow_left₀ (hρ x hx).1 (hρ x hx).2 m)
  · rw [powerWeight_eq_zero_of_not_mem hx]
    exact pow_nonneg hC m

theorem integrable_powerWeight {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C) :
    Integrable (powerWeight m K ρ) volume := by
  have hi : Integrable (K.indicator (fun _ : Fin n → ℝ => C ^ m)) volume := by
    rw [integrable_indicator_iff hK]
    exact integrableOn_const hfin
  apply hi.mono' (measurable_powerWeight hK hρ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (powerWeight_nonneg (fun x hx => (hb x hx).1) x)]
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact powerWeight_le hC hb x
  · simp [powerWeight, hx]

theorem powerMass_pos {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    0 < powerMass m K ρ := by
  have hnn : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C :=
    fun x hx => ⟨hc.le.trans (hb x hx).1, (hb x hx).2⟩
  have hi := integrable_powerWeight hK hfin hρ hC hnn (m := m)
  have hic : Integrable (K.indicator (fun _ : Fin n → ℝ => c ^ m)) volume := by
    rw [integrable_indicator_iff hK]
    exact integrableOn_const hfin
  have hl : (volume K).toReal * c ^ m ≤ powerMass m K ρ := by
    change volume.real K * c ^ m ≤ powerMass m K ρ
    rw [← smul_eq_mul, ← integral_indicator_const _ hK]
    apply integral_mono hic hi
    intro x
    by_cases hx : x ∈ K
    · simp only [powerWeight, Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ hc.le (hb x hx).1 m
    · simp [powerWeight, hx]
  exact (mul_pos (ENNReal.toReal_pos hpos hfin) (pow_pos hc m)).trans_le hl

theorem measurable_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    Measurable (powerDensity m K ρ) := (measurable_powerWeight hK hρ).div_const _

theorem powerDensity_eq_zero_of_not_mem {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∉ K) :
    powerDensity m K ρ x = 0 := by simp [powerDensity, powerWeight, hx]

theorem powerDensity_nonneg {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hρ : ∀ x ∈ K, 0 ≤ ρ x) (x : Fin n → ℝ) :
    0 ≤ powerDensity m K ρ x :=
  div_nonneg (powerWeight_nonneg hρ x) (integral_nonneg (powerWeight_nonneg hρ))

theorem powerDensity_le {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hZ : 0 < powerMass m K ρ) (hC : 0 ≤ C)
    (hρ : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C) (x : Fin n → ℝ) :
    powerDensity m K ρ x ≤ C ^ m / powerMass m K ρ :=
  div_le_div_of_nonneg_right (powerWeight_le hC hρ x) hZ.le

theorem integrable_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hi : Integrable (powerWeight m K ρ) volume) :
    Integrable (powerDensity m K ρ) volume := hi.div_const _

theorem integral_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hZ : powerMass m K ρ ≠ 0) :
    (∫ x, powerDensity m K ρ x) = 1 := by
  change (∫ x, powerWeight m K ρ x / powerMass m K ρ) = 1
  rw [integral_div, ← powerMass, div_self hZ]

theorem isProbabilityDensity_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    IsProbabilityDensity n (powerDensity m K ρ) := by
  have hnn : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C :=
    fun x hx => ⟨hc.le.trans (hb x hx).1, (hb x hx).2⟩
  exact ⟨measurable_powerDensity hK hρ,
    powerDensity_nonneg (fun x hx => (hnn x hx).1),
    integrable_powerDensity (integrable_powerWeight hK hfin hρ hC hnn),
    integral_powerDensity (powerMass_pos hK hfin hpos hρ hc hC hb).ne'⟩

theorem integrable_negMulLog_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fun x => Real.negMulLog (powerDensity m K ρ x)) volume := by
  have hnn : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C :=
    fun x hx => ⟨hc.le.trans (hb x hx).1, (hb x hx).2⟩
  apply integrable_negMulLog_of_bounded_support hK hfin (measurable_powerDensity hK hρ)
  · intro x
    exact ⟨powerDensity_nonneg (fun x hx => (hnn x hx).1) x,
      powerDensity_le (powerMass_pos hK hfin hpos hρ hc hC hb) hC hnn x⟩
  · exact fun _ hx => powerDensity_eq_zero_of_not_mem hx

theorem negMulLog_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hZ : 0 < powerMass m K ρ)
    (hρ : ∀ x ∈ K, 0 < ρ x) (x : Fin n → ℝ) :
    Real.negMulLog (powerDensity m K ρ x) =
      powerDensity m K ρ x * (Real.log (powerMass m K ρ) - (m : ℝ) * Real.log (ρ x)) := by
  by_cases hx : x ∈ K
  · have hr := hρ x hx
    simp only [powerDensity, powerWeight, Set.indicator_of_mem hx, Real.negMulLog_def]
    rw [Real.log_div (pow_ne_zero m hr.ne') hZ.ne', Real.log_pow]
    ring
  · simp [powerDensity_eq_zero_of_not_mem hx]

theorem integrable_powerDensity_mul_log {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    Integrable (fun x => powerDensity m K ρ x * Real.log (ρ x)) volume := by
  have hf := isProbabilityDensity_powerDensity (m := m) hK hfin hpos hρ hc hC.le hb
  have hi := hf.2.2.1.const_mul (|Real.log c| + |Real.log C|)
  apply hi.mono' ((measurable_powerDensity hK hρ).mul hρ.log).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · have hl : Real.log c ≤ Real.log (ρ x) := Real.log_le_log hc (hb x hx).1
    have hu : Real.log (ρ x) ≤ Real.log C :=
      Real.log_le_log (hc.trans_le (hb x hx).1) (hb x hx).2
    have ha : |Real.log (ρ x)| ≤ |Real.log c| + |Real.log C| := by
      apply abs_le.mpr
      constructor
      · have := neg_abs_le (Real.log c)
        have := abs_nonneg (Real.log C)
        linarith
      · have := le_abs_self (Real.log C)
        have := abs_nonneg (Real.log c)
        linarith
    change ‖powerDensity m K ρ x * Real.log (ρ x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.2.1 x)]
    exact (mul_le_mul_of_nonneg_left ha (hf.2.1 x)).trans_eq (mul_comm _ _)
  · simp [powerDensity_eq_zero_of_not_mem hx]

theorem differentialEntropy_powerDensity {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    differentialEntropy (powerDensity m K ρ) volume = Real.log (powerMass m K ρ) -
      (m : ℝ) * ∫ x, powerDensity m K ρ x * Real.log (ρ x) := by
  have hZ := powerMass_pos (m := m) hK hfin hpos hρ hc hC.le hb
  have hf := isProbabilityDensity_powerDensity (m := m) hK hfin hpos hρ hc hC.le hb
  have hi := integrable_powerDensity_mul_log (m := m) hK hfin hpos hρ hc hC hb
  have he : (fun x => Real.negMulLog (powerDensity m K ρ x)) =
      (fun x => Real.log (powerMass m K ρ) * powerDensity m K ρ x -
        (m : ℝ) * (powerDensity m K ρ x * Real.log (ρ x))) := by
    funext x
    rw [negMulLog_powerDensity hZ (fun x hx => hc.trans_le (hb x hx).1)]
    ring
  rw [differentialEntropy, he,
    integral_sub (hf.2.2.1.const_mul _) (hi.const_mul _),
    integral_const_mul, integral_const_mul, hf.2.2.2, mul_one]

end EntropicRogersShephard
