import EntropicRogersShephard.FiberDifferenceBounds
import EntropicRogersShephard.BodyEntropyBound

/-! Volume-preserving coordinate concatenation and the actual fiber-body upper bound. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def coordinateJoin (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃L[ℝ] (Fin (n + m) → ℝ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + m) => ℝ) finSumFinEquiv)).toContinuousLinearEquiv

theorem volume_preserving_coordinateJoin (n m : ℕ) :
    MeasurePreserving (coordinateJoin n m) volume volume := by
  have hs := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin m => ℝ)
  have hr := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + m) => ℝ) (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
  convert hr.comp hs using 1
  rfl

theorem volume_coordinateJoin_image {n m : ℕ}
    (A : Set ((Fin n → ℝ) × (Fin m → ℝ))) :
    volume ((coordinateJoin n m) '' A) = volume A := by
  let e := (coordinateJoin n m).toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e volume volume := volume_preserving_coordinateJoin n m
  change volume (e '' A) = volume A
  rw [← hp.map_eq, e.map_apply, Set.preimage_image_eq _ e.injective]

def joinedFiberBody {n m : ℕ} (K : Set (Fin n → ℝ)) (ρ : (Fin n → ℝ) → ℝ) :
    Set (Fin (n + m) → ℝ) := (coordinateJoin n m) '' fiberBody n m K ρ

theorem isCompact_joinedFiberBody {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} {C : ℝ} (hK : IsCompact K) (hρ : ContinuousOn ρ K)
    (hb : ∀ x ∈ K, ρ x ≤ C) : IsCompact (joinedFiberBody (m := m) K ρ) :=
  (isCompact_fiberBody hK hρ hb).image (coordinateJoin n m).continuous

theorem convex_joinedFiberBody {n m : ℕ} {K : Set (Fin n → ℝ)}
    {ρ : (Fin n → ℝ) → ℝ} (hρ : ConcaveOn ℝ K ρ) :
    Convex ℝ (joinedFiberBody (m := m) K ρ) :=
  (convex_fiberBody n m K ρ hρ).linear_image (coordinateJoin n m).toLinearMap

theorem volume_joinedFiberBody {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) : volume (joinedFiberBody (m := m) K ρ) = volume (fiberBody n m K ρ) :=
  volume_coordinateJoin_image _

theorem uniformDensity_joinedFiberBody {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    uniformDensity (joinedFiberBody K ρ) (coordinateJoin n m p) = fiberUniformDensity K ρ p := by
  have he : coordinateJoin n m p ∈ joinedFiberBody K ρ ↔ p ∈ fiberBody n m K ρ := by
    constructor
    · rintro ⟨q, hq, heq⟩
      exact (coordinateJoin n m).injective heq ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  by_cases hp : p ∈ fiberBody n m K ρ
  · simp [uniformDensity, fiberUniformDensity, hp, he.mpr hp, volume_joinedFiberBody]
  · have hj : coordinateJoin n m p ∉ joinedFiberBody K ρ := fun h => hp (he.mp h)
    simp [uniformDensity, fiberUniformDensity, hp, hj]

theorem crossDifferenceDensity_joinedFiberBody {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    crossDifferenceDensity (uniformDensity (joinedFiberBody K ρ))
      (uniformDensity (joinedFiberBody K ρ)) (coordinateJoin n m z) =
        fiberDifferenceDensity K ρ z := by
  have h := (volume_preserving_coordinateJoin n m).integral_comp
    (coordinateJoin n m).toHomeomorph.measurableEmbedding
    (fun x => uniformDensity (joinedFiberBody K ρ) x *
      uniformDensity (joinedFiberBody K ρ) (x - coordinateJoin n m z))
  simp_rw [← (coordinateJoin n m).map_sub, uniformDensity_joinedFiberBody] at h
  exact h.symm

theorem differentialEntropy_joinedFiberBody {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) :
    differentialEntropy (uniformDensity (joinedFiberBody (m := m) K ρ)) volume =
      differentialEntropy (fiberUniformDensity (m := m) K ρ) volume := by
  have h := (volume_preserving_coordinateJoin n m).integral_comp
    (coordinateJoin n m).toHomeomorph.measurableEmbedding
    (fun x => Real.negMulLog (uniformDensity (joinedFiberBody K ρ) x))
  simp_rw [uniformDensity_joinedFiberBody] at h
  exact h.symm

theorem differentialEntropy_joinedFiberDifference {n m : ℕ} (K : Set (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) :
    differentialEntropy (crossDifferenceDensity (uniformDensity (joinedFiberBody (m := m) K ρ))
      (uniformDensity (joinedFiberBody K ρ))) volume =
        differentialEntropy (fiberDifferenceDensity (m := m) K ρ) volume := by
  have h := (volume_preserving_coordinateJoin n m).integral_comp
    (coordinateJoin n m).toHomeomorph.measurableEmbedding
    (fun x => Real.negMulLog (crossDifferenceDensity (uniformDensity (joinedFiberBody K ρ))
      (uniformDensity (joinedFiberBody K ρ)) x))
  simp_rw [crossDifferenceDensity_joinedFiberBody] at h
  exact h.symm

theorem fiber_body_entropy_increment_bound {n m : ℕ} [NeZero (n + m)]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hcont : ContinuousOn ρ K) (hconc : ConcaveOn ℝ K ρ)
    (hc : 0 < c) (hC : 0 ≤ C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    differentialEntropy (fiberDifferenceDensity (m := m) K ρ) volume -
      differentialEntropy (fiberUniformDensity (m := m) K ρ) volume ≤ F (n + m) := by
  have hB := isCompact_joinedFiberBody (m := m) hK hcont (fun x hx => (hb x hx).2)
  have hV : volume (joinedFiberBody (m := m) K ρ) ≠ 0 := by
    rw [volume_joinedFiberBody]
    exact (volume_fiberBody_pos hK.measurableSet hK.measure_ne_top hpos hρ hc hC hb).ne'
  have h := uniform_convex_body_entropy_bound hB (convex_joinedFiberBody hconc) hV
  rw [differentialEntropy_joinedFiberDifference, differentialEntropy_joinedFiberBody] at h
  exact h

theorem fiber_difference_entropy_upper_bound {n m : ℕ} [NeZero (n + m)]
    {K : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → ℝ} {c C : ℝ}
    (hK : IsCompact K) (hpos : volume K ≠ 0) (hρ : Measurable ρ)
    (hcont : ContinuousOn ρ K) (hconc : ConcaveOn ℝ K ρ)
    (hc : 0 < c) (hC : 0 < C) (hb : ∀ x ∈ K, ρ x ∈ Icc c C) :
    differentialEntropy (fiberDifferenceDensity (m := m) K ρ) volume ≤
      differentialEntropy (powerDensity m K ρ) volume + Real.log (volume (simplex m 1)).toReal +
        (m : ℝ) * (∫ x, powerDensity m K ρ x * Real.log (ρ x)) + F (n + m) := by
  have h := fiber_body_entropy_increment_bound hK hpos hρ hcont hconc hc hC.le hb (m := m)
  rw [differentialEntropy_fiberUniformDensity hK.measurableSet hK.measure_ne_top hpos hρ hc hC hb] at h
  simpa only [add_comm] using (sub_le_iff_le_add).mp h

end EntropicRogersShephard
