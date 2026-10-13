import EntropicRogersShephard.PowerDensity

/-! Measurability, compactness and volume of the simplex fiber lift. -/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem measurableSet_fiberBody {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hK : MeasurableSet K) (hρ : Measurable ρ) :
    MeasurableSet (fiberBody n m K ρ) := by
  have hn : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) | ∀ i, 0 ≤ p.2 i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  have hl : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) | ∑ i, p.2 i ≤ ρ p.1} :=
    measurableSet_le (by fun_prop) (hρ.comp measurable_fst)
  exact (hK.preimage measurable_fst).inter (hn.inter hl)

theorem fiberBody_subset_product {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hρ : ∀ x ∈ K, ρ x ≤ C) :
    fiberBody n m K ρ ⊆ K ×ˢ simplex m C := by
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans (hρ p.1 hp.1)⟩

theorem isCompact_fiberBody {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hK : IsCompact K)
    (hρ : ContinuousOn ρ K) (hb : ∀ x ∈ K, ρ x ≤ C) :
    IsCompact (fiberBody n m K ρ) := by
  let T := K ×ˢ simplex m C
  have hT : IsCompact T := hK.prod (isCompact_simplex m C)
  have hc : ContinuousOn (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      (∑ i, p.2 i) - ρ p.1) T :=
    (by fun_prop : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => ∑ i, p.2 i)).continuousOn.sub
      (hρ.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have he : fiberBody n m K ρ = T ∩
      (fun p : (Fin n → ℝ) × (Fin m → ℝ) => (∑ i, p.2 i) - ρ p.1) ⁻¹' Iic 0 := by
    ext p
    constructor
    · intro hp
      exact ⟨fiberBody_subset_product hb hp, sub_nonpos.mpr hp.2.2⟩
    · intro hp
      exact ⟨hp.1.1, hp.1.2.1, sub_nonpos.mp hp.2⟩
  rw [he]
  exact hT.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hT.isClosed isClosed_Iic)
    inter_subset_left

theorem fiberBody_slice {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) [Decidable (x ∈ K)] :
    Prod.mk x ⁻¹' fiberBody n m K ρ = if x ∈ K then simplex m (ρ x) else ∅ := by
  by_cases hx : x ∈ K <;> ext y <;> simp [fiberBody, hx]

theorem volume_fiberBody {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    volume (fiberBody n m K ρ) =
      ENNReal.ofReal (powerMass m K ρ) * volume (simplex m 1) := by
  classical
  have hnn : ∀ x ∈ K, ρ x ∈ Icc (0 : ℝ) C :=
    fun x hx => ⟨hc.le.trans (hb x hx).1, (hb x hx).2⟩
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply (measurableSet_fiberBody hK hρ)]
  have he : (fun x => volume (Prod.mk x ⁻¹' fiberBody n m K ρ)) =
      (fun x => ENNReal.ofReal (powerWeight m K ρ x) * volume (simplex m 1)) := by
    funext x
    rw [fiberBody_slice]
    by_cases hx : x ∈ K
    · rw [if_pos hx, powerWeight, Set.indicator_of_mem hx,
        volume_simplex_pos m (hc.trans_le (hb x hx).1)]
    · simp [hx, powerWeight]
  rw [he, lintegral_mul_const' _ _ (volume_simplex_ne_top m 1),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_powerWeight hK hfin hρ hC hnn)
      (Filter.Eventually.of_forall (powerWeight_nonneg (fun x hx => (hnn x hx).1)))]
  rfl

theorem volume_fiberBody_real {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    (volume (fiberBody n m K ρ)).toReal =
      powerMass m K ρ * (volume (simplex m 1)).toReal := by
  have hnn : 0 ≤ powerMass m K ρ := integral_nonneg (powerWeight_nonneg
    (fun x hx => hc.le.trans (hb x hx).1))
  rw [volume_fiberBody hK hfin hρ hc hC hb, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hnn]

theorem volume_fiberBody_pos {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ} (hK : MeasurableSet K)
    (hfin : volume K ≠ ∞) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    0 < volume (fiberBody n m K ρ) := by
  rw [volume_fiberBody hK hfin hρ hc hC hb]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (powerMass_pos hK hfin hpos hρ hc hC hb)).ne'
    (volume_unit_simplex_pos m).ne'

end EntropicRogersShephard
