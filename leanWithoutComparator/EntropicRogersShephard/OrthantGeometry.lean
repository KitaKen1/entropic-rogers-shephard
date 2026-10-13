import EntropicRogersShephard.SimplexDensity

/-!
Closed overlap superlevels, decomposed into coordinate orthants.
The simplex volumes on the two coordinate blocks remain symbolic.
-/

open MeasureTheory Set Finset
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace EntropicRogersShephard

/-- Coordinate simplex on an arbitrary finite index type, including the empty type. -/
def simplexOn (ι : Type*) [Fintype ι] (a : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ a}

theorem isClosed_simplexOn (ι : Type*) [Fintype ι] (a : ℝ) :
    IsClosed (simplexOn ι a) := by
  have hcoords : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact hcoords.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem simplexOn_pos_eq_smul (ι : Type*) [Fintype ι] {a : ℝ} (ha : 0 < a) :
    simplexOn ι a = (fun y : ι → ℝ => a • y) '' simplexOn ι 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨a⁻¹ • x, ?_, ?_⟩
    · constructor
      · intro i
        exact mul_nonneg (inv_nonneg.mpr ha.le) (hx.1 i)
      · change ∑ i, a⁻¹ * x i ≤ 1
        rw [← Finset.mul_sum]
        calc
          a⁻¹ * ∑ i, x i ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hx.2 (inv_nonneg.mpr ha.le)
          _ = 1 := inv_mul_cancel₀ ha.ne'
    · simp [smul_smul, ha.ne']
  · rintro ⟨y, hy, rfl⟩
    constructor
    · intro i
      exact mul_nonneg ha.le (hy.1 i)
    · change ∑ i, a * y i ≤ a
      rw [← Finset.mul_sum]
      simpa using mul_le_mul_of_nonneg_left hy.2 ha.le

theorem volume_simplexOn_pos (ι : Type*) [Fintype ι] {a : ℝ} (ha : 0 < a) :
    volume (simplexOn ι a) =
      ENNReal.ofReal (a ^ Fintype.card ι) * volume (simplexOn ι 1) := by
  rw [simplexOn_pos_eq_smul ι ha]
  have he : (fun y : ι → ℝ => a • y) = AffineMap.homothety (0 : ι → ℝ) a := by
    funext y
    simp [AffineMap.homothety_apply]
  rw [he, Measure.addHaar_image_homothety]
  simp [abs_of_nonneg (pow_nonneg ha.le (Fintype.card ι))]

def coordinateOrthant (m : ℕ) (s : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {z | (∀ i, i ∈ s → 0 ≤ z i) ∧ (∀ i, i ∉ s → z i ≤ 0)}

def signFlip {m : ℕ} (s : Finset (Fin m)) (z : Fin m → ℝ) (i : Fin m) : ℝ :=
  if i ∈ s then z i else -z i

theorem measurePreserving_signFlip (m : ℕ) (s : Finset (Fin m)) :
    MeasurePreserving (signFlip s) volume volume := by
  have h : ∀ i : Fin m, MeasurePreserving (fun r : ℝ => if i ∈ s then r else -r)
      volume volume := by
    intro i
    by_cases hi : i ∈ s
    · simp only [hi, ite_true]
      have hid : (fun r : ℝ => r) = id := rfl
      rw [hid]
      exact MeasurePreserving.id _
    · simpa only [hi, ite_false] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact volume_preserving_pi h

theorem positiveMass_on_orthant {m : ℕ} {s : Finset (Fin m)} {z : Fin m → ℝ}
    (hz : z ∈ coordinateOrthant m s) :
    positiveMass z = ∑ i : {i : Fin m // i ∈ s}, z i := by
  have h₁ : (∑ i : {i : Fin m // i ∈ s}, max (z i) 0) = ∑ i : {i : Fin m // i ∈ s}, z i := by
    apply Finset.sum_congr rfl
    intro i _
    exact max_eq_left (hz.1 i i.2)
  have h₂ : (∑ i : {i : Fin m // i ∉ s}, max (z i) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_right (hz.2 i i.2)
  have hsinst : Subtype.fintype (fun i : Fin m => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  have huniv := congrArg (fun F : Fintype {i : Fin m // i ∈ s} => @Finset.univ _ F) hsinst
  calc
    positiveMass z = (∑ i : {i : Fin m // i ∈ s}, max (z i) 0) +
      ∑ i : {i : Fin m // i ∉ s}, max (z i) 0 :=
      by
        have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun i => max (z i) 0)
        rw [huniv] at h
        exact h.symm
    _ = ∑ i : {i : Fin m // i ∈ s}, z i := by rw [h₁, h₂, add_zero]

theorem negativeMass_on_orthant {m : ℕ} {s : Finset (Fin m)} {z : Fin m → ℝ}
    (hz : z ∈ coordinateOrthant m s) :
    negativeMass z = ∑ i : {i : Fin m // i ∉ s}, -z i := by
  have h₁ : (∑ i : {i : Fin m // i ∈ s}, max (-z i) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_right (neg_nonpos.mpr (hz.1 i i.2))
  have h₂ : (∑ i : {i : Fin m // i ∉ s}, max (-z i) 0) =
      ∑ i : {i : Fin m // i ∉ s}, -z i := by
    apply Finset.sum_congr rfl
    intro i _
    exact max_eq_left (neg_nonneg.mpr (hz.2 i i.2))
  have hsinst : Subtype.fintype (fun i : Fin m => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  have huniv := congrArg (fun F : Fintype {i : Fin m // i ∈ s} => @Finset.univ _ F) hsinst
  calc
    negativeMass z = (∑ i : {i : Fin m // i ∈ s}, max (-z i) 0) +
      ∑ i : {i : Fin m // i ∉ s}, max (-z i) 0 :=
      by
        have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun i => max (-z i) 0)
        rw [huniv] at h
        exact h.symm
    _ = ∑ i : {i : Fin m // i ∉ s}, -z i := by rw [h₁, h₂, zero_add]

def orthantSector (m : ℕ) (s : Finset (Fin m)) (u v : ℝ) : Set (Fin m → ℝ) :=
  {z | z ∈ coordinateOrthant m s ∧ positiveMass z ≤ u ∧ negativeMass z ≤ v}

theorem orthantSector_eq_preimage (m : ℕ) (s : Finset (Fin m)) (u v : ℝ) :
    orthantSector m s u v =
      (fun z => MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => ℝ)
        (fun i => i ∈ s) (signFlip s z)) ⁻¹'
      (simplexOn {i : Fin m // i ∈ s} u ×ˢ simplexOn {i : Fin m // i ∉ s} v) := by
  ext z
  have hcoords : z ∈ coordinateOrthant m s ↔
      (∀ i : {i : Fin m // i ∈ s}, 0 ≤ z i) ∧
        (∀ i : {i : Fin m // i ∉ s}, 0 ≤ -z i) := by
    constructor
    · intro hz
      exact ⟨fun i => hz.1 i i.2, fun i => neg_nonneg.mpr (hz.2 i i.2)⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun i hi => h₁ ⟨i, hi⟩, fun i hi => neg_nonneg.mp (h₂ ⟨i, hi⟩)⟩
  change (z ∈ coordinateOrthant m s ∧ positiveMass z ≤ u ∧ negativeMass z ≤ v) ↔
    ((∀ i : {i : Fin m // i ∈ s}, 0 ≤ signFlip s z i) ∧
      (∑ i : {i : Fin m // i ∈ s}, signFlip s z i) ≤ u) ∧
    ((∀ i : {i : Fin m // i ∉ s}, 0 ≤ signFlip s z i) ∧
      (∑ i : {i : Fin m // i ∉ s}, signFlip s z i) ≤ v)
  have hpos (i : {i : Fin m // i ∈ s}) : signFlip s z i = z i := by
    simp [signFlip, i.property]
  have hneg (i : {i : Fin m // i ∉ s}) : signFlip s z i = -z i := by
    simp [signFlip, i.property]
  simp only [hpos, hneg]
  constructor
  · rintro ⟨hz, hp, hn⟩
    rw [positiveMass_on_orthant hz] at hp
    rw [negativeMass_on_orthant hz] at hn
    exact ⟨⟨(hcoords.mp hz).1, hp⟩, ⟨(hcoords.mp hz).2, hn⟩⟩
  · rintro ⟨⟨h₁, hp⟩, ⟨h₂, hn⟩⟩
    have hz := hcoords.mpr ⟨h₁, h₂⟩
    rw [← positiveMass_on_orthant hz] at hp
    rw [← negativeMass_on_orthant hz] at hn
    exact ⟨hz, hp, hn⟩

theorem measurableSet_orthantSector (m : ℕ) (s : Finset (Fin m)) (u v : ℝ) :
    MeasurableSet (orthantSector m s u v) := by
  rw [orthantSector_eq_preimage]
  exact ((isClosed_simplexOn _ u).measurableSet.prod (isClosed_simplexOn _ v).measurableSet).preimage
    ((volume_preserving_piEquivPiSubtypeProd (fun _ : Fin m => ℝ) (fun i => i ∈ s)).measurable.comp
      (measurePreserving_signFlip m s).measurable)

theorem volume_orthantSector (m : ℕ) (s : Finset (Fin m)) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    volume (orthantSector m s u v) =
      (ENNReal.ofReal (u ^ Fintype.card {i : Fin m // i ∈ s}) *
        volume (simplexOn {i : Fin m // i ∈ s} 1)) *
      (ENNReal.ofReal (v ^ Fintype.card {i : Fin m // i ∉ s}) *
        volume (simplexOn {i : Fin m // i ∉ s} 1)) := by
  rw [orthantSector_eq_preimage]
  have hp₀ := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin m => ℝ)
    (fun i => i ∈ s)).comp (measurePreserving_signFlip m s)
  simp only [Function.comp_def] at hp₀
  have hp : MeasurePreserving (fun z =>
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => ℝ)
        (fun i => i ∈ s) (signFlip s z)) volume
      ((volume : Measure ({i : Fin m // i ∈ s} → ℝ)).prod
        (volume : Measure ({i : Fin m // i ∉ s} → ℝ))) := by
    convert! hp₀ using 1
    congr 3 <;> exact Subsingleton.elim _ _
  rw [hp.measure_preimage
    ((isClosed_simplexOn _ u).measurableSet.prod (isClosed_simplexOn _ v).measurableSet).nullMeasurableSet]
  rw [Measure.prod_prod, volume_simplexOn_pos _ hu, volume_simplexOn_pos _ hv]

theorem coordinateOrthant_cover (m : ℕ) (z : Fin m → ℝ) :
    ∃ s : Finset (Fin m), z ∈ coordinateOrthant m s := by
  classical
  refine ⟨Finset.univ.filter (fun i => 0 ≤ z i), ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    have hn : ¬0 ≤ z i := by simpa using hi
    exact (lt_of_not_ge hn).le

theorem aedisjoint_coordinateOrthants (m : ℕ) {s t : Finset (Fin m)} (hst : s ≠ t) :
    AEDisjoint volume (coordinateOrthant m s) (coordinateOrthant m t) := by
  obtain ⟨i, hi⟩ := Finset.symmDiff_nonempty.mpr hst
  apply measure_mono_null (t := {z : Fin m → ℝ | z i = 0})
  · intro z hz
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact le_antisymm (hz.2.2 i hi.2) (hz.1.1 i hi.1)
    · exact le_antisymm (hz.1.2 i hi.2) (hz.2.1 i hi.1)
  · simpa only [volume_pi] using Measure.pi_hyperplane (fun _ : Fin m => (volume : Measure ℝ)) i 0

theorem overlapRadius_ge_iff {m : ℕ} (a b t : ℝ) (z : Fin m → ℝ) (ht : 0 < t) :
    t ≤ overlapRadius a b z ↔ positiveMass z ≤ a - t ∧ negativeMass z ≤ b - t := by
  rw [overlapRadius, le_max_iff, or_iff_right (not_le_of_gt ht), rawRadius, le_min_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem overlap_superlevel_eq_union_sectors (m : ℕ) (a b t : ℝ) (ht : 0 < t) :
    {z : Fin m → ℝ | t ≤ overlapRadius a b z} =
      ⋃ s : Finset (Fin m), orthantSector m s (a - t) (b - t) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := coordinateOrthant_cover m z
    exact ⟨s, hs, (overlapRadius_ge_iff a b t z ht).mp hz⟩
  · rintro ⟨s, _, hp, hn⟩
    exact (overlapRadius_ge_iff a b t z ht).mpr ⟨hp, hn⟩

/-- Exact closed-superlevel volume, with no factorial volume calculation. -/
theorem volume_overlap_superlevel (m : ℕ) {a b t : ℝ}
    (ht : 0 < t) (hta : t < a) (htb : t < b) :
    volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} =
      ∑ s : Finset (Fin m),
        (ENNReal.ofReal ((a - t) ^ Fintype.card {i : Fin m // i ∈ s}) *
          volume (simplexOn {i : Fin m // i ∈ s} 1)) *
        (ENNReal.ofReal ((b - t) ^ Fintype.card {i : Fin m // i ∉ s}) *
          volume (simplexOn {i : Fin m // i ∉ s} 1)) := by
  rw [overlap_superlevel_eq_union_sectors m a b t ht]
  rw [measure_iUnion₀]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    exact volume_orthantSector m s (sub_pos.mpr hta) (sub_pos.mpr htb)
  · intro s t hst
    exact (aedisjoint_coordinateOrthants m hst).mono
      (fun _ hz => hz.1) (fun _ hz => hz.1)
  · intro s
    exact (measurableSet_orthantSector m s (a - t) (b - t)).nullMeasurableSet

end EntropicRogersShephard
