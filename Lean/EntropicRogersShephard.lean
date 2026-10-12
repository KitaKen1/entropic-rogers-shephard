/-
# Intermediate results for the entropic Rogers–Shephard inequality

The full target is defined below as `SharpEntropicRogersShephard`;
it is not yet proved. All theorems in this file are intermediate results.
-/

import LeanPool.Isoperimetric.BrunnMinkowski
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-! ## Scalar -/

open Finset Real


namespace EntropicRogersShephard

theorem harmonic_term_bound (m k : ℝ) (hm : 0 < m) (hk : 0 ≤ k) (hkm : k ≤ m) :
    1 / (2 * m - k) ≤ 1 / (2 * m) + k / (2 * m ^ 2) := by
  have hp : 0 < 2 * m - k := by linarith
  apply (div_le_iff₀ hp).2
  field_simp
  nlinarith

theorem neg_log_one_sub_lower (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    q + q ^ 2 / 2 ≤ -Real.log (1 - q) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |q| < 1 by rwa [abs_of_nonneg hq])
  have hsum := Summable.sum_le_tsum (Finset.range 2)
    (fun i _ => show 0 ≤ q ^ (i + 1) / ((i : ℝ) + 1) by positivity) hs.summable
  rw [hs.tsum_eq] at hsum
  norm_num [Finset.sum_range_succ] at hsum
  exact hsum

theorem scale_gap_lower (m q : ℝ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hq1 : q < 1) :
    q ^ 2 / 4 ≤ m / 2 * (-Real.log (1 - q) - q) - (m - 1) / 4 * q ^ 2 := by
  have hlog := neg_log_one_sub_lower q hq hq1
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hlog)]


end EntropicRogersShephard

/-! ## Simplex -/

open Set Finset

namespace EntropicRogersShephard

/-- The full-dimensional coordinate simplex of size `a`. Negative sizes give the empty set. -/
def simplex (m : ℕ) (a : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ a}

def positiveMass {m : ℕ} (z : Fin m → ℝ) : ℝ := ∑ i, max (z i) 0

def negativeMass {m : ℕ} (z : Fin m → ℝ) : ℝ := ∑ i, max (-z i) 0

def lowerCorner {m : ℕ} (z : Fin m → ℝ) : Fin m → ℝ := fun i => max (z i) 0

def rawRadius {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) : ℝ :=
  min (a - positiveMass z) (b - negativeMass z)

def overlapRadius {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) : ℝ :=
  max 0 (rawRadius a b z)

theorem positiveMass_nonneg {m : ℕ} (z : Fin m → ℝ) : 0 ≤ positiveMass z :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem negativeMass_nonneg {m : ℕ} (z : Fin m → ℝ) : 0 ≤ negativeMass z :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem sum_eq_positiveMass_sub_negativeMass {m : ℕ} (z : Fin m → ℝ) :
    ∑ i, z i = positiveMass z - negativeMass z := by
  rw [positiveMass, negativeMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ z i
  · rw [max_eq_left hi, max_eq_right (by linarith : -z i ≤ 0)]
    ring
  · rw [max_eq_right (le_of_not_ge hi), max_eq_left (by linarith : 0 ≤ -z i)]
    ring

theorem mem_simplex_coordinate_le {m : ℕ} {a : ℝ} {x : Fin m → ℝ}
    (hx : x ∈ simplex m a) (i : Fin m) : x i ≤ a := by
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

theorem simplex_empty_of_neg (m : ℕ) {a : ℝ} (ha : a < 0) : simplex m a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx.1 i)
  linarith [hx.2]

theorem simplex_zero (m : ℕ) : simplex m 0 = {0} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    funext i
    exact le_antisymm (mem_simplex_coordinate_le hx i) (hx.1 i)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simp [simplex]

theorem convex_simplex (m : ℕ) (a : ℝ) : Convex ℝ (simplex m a) := by
  intro x hx y hy s t hs ht hst
  constructor
  · intro i
    exact add_nonneg (mul_nonneg hs (hx.1 i)) (mul_nonneg ht (hy.1 i))
  · change ∑ i, (s * x i + t * y i) ≤ a
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      s * ∑ i, x i + t * ∑ i, y i ≤ s * a + t * a :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 hs) (mul_le_mul_of_nonneg_left hy.2 ht)
      _ = a := by rw [← add_mul, hst, one_mul]

theorem isClosed_simplex (m : ℕ) (a : ℝ) : IsClosed (simplex m a) := by
  have hcoords : IsClosed {x : Fin m → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact hcoords.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem isCompact_simplex (m : ℕ) (a : ℝ) : IsCompact (simplex m a) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin m → ℝ))
    (b := fun _ => a)) (isClosed_simplex m a)
  intro x hx
  exact ⟨hx.1, fun i => mem_simplex_coordinate_le hx i⟩

/-- Exact geometric reduction of two differently scaled simplex constraints.
The raw radius is used so that infeasible intersections remain empty. -/
theorem mem_overlap_iff_shifted_simplex {m : ℕ} (a b : ℝ) (z x : Fin m → ℝ) :
    (x ∈ simplex m a ∧ x - z ∈ simplex m b) ↔
      x - lowerCorner z ∈ simplex m (rawRadius a b z) := by
  have hsum : ∑ i, (x - lowerCorner z) i = ∑ i, x i - positiveMass z := by
    simp [lowerCorner, positiveMass, Finset.sum_sub_distrib]
  have hz : ∑ i, z i = positiveMass z - negativeMass z :=
    sum_eq_positiveMass_sub_negativeMass z
  have hsumz : ∑ i, (x - z) i = ∑ i, x i - ∑ i, z i := by
    simp [Finset.sum_sub_distrib]
  change (((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ a) ∧
    ((∀ i, 0 ≤ (x - z) i) ∧ ∑ i, (x - z) i ≤ b)) ↔
    ((∀ i, 0 ≤ (x - lowerCorner z) i) ∧
      ∑ i, (x - lowerCorner z) i ≤ rawRadius a b z)
  rw [hsum, hsumz, hz, rawRadius, le_min_iff]
  constructor
  · rintro ⟨⟨hx, hxa⟩, ⟨hxz, hxb⟩⟩
    refine ⟨?_, by constructor <;> linarith⟩
    intro i
    have hi : max (z i) 0 ≤ x i := max_le (by simpa using hxz i) (hx i)
    simpa [lowerCorner] using sub_nonneg.mpr hi
  · rintro ⟨hx, ha, hb⟩
    have hi (i : Fin m) : max (z i) 0 ≤ x i := by
      simpa [lowerCorner] using sub_nonneg.mp (hx i)
    refine ⟨⟨fun i => (le_max_right _ _).trans (hi i), by linarith⟩,
      ⟨?_, by linarith⟩⟩
    intro i
    exact sub_nonneg.mpr ((le_max_left _ _).trans (hi i))

theorem overlap_eq_translated_simplex {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) :
    {x | x ∈ simplex m a ∧ x - z ∈ simplex m b} =
      (fun y => y + lowerCorner z) '' simplex m (rawRadius a b z) := by
  ext x
  rw [Set.mem_ofPred_eq, mem_overlap_iff_shifted_simplex]
  constructor
  · intro hx
    exact ⟨x - lowerCorner z, hx, sub_add_cancel _ _⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem overlapRadius_nonneg {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) :
    0 ≤ overlapRadius a b z := le_max_left _ _

theorem overlapRadius_le_right {m : ℕ} (a b : ℝ) (z : Fin m → ℝ) (hb : 0 ≤ b) :
    overlapRadius a b z ≤ b := by
  apply max_le hb
  exact (min_le_right _ _).trans (sub_le_self _ (negativeMass_nonneg z))

theorem overlapRadius_gt_iff {m : ℕ} (a b t : ℝ) (z : Fin m → ℝ) (ht : 0 ≤ t) :
    t < overlapRadius a b z ↔ positiveMass z < a - t ∧ negativeMass z < b - t := by
  rw [overlapRadius, lt_max_iff, or_iff_right (not_lt.mpr ht), rawRadius, lt_min_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end EntropicRogersShephard

/-! ## SimplexVolume -/

open Set Finset MeasureTheory
open scoped ENNReal

namespace EntropicRogersShephard

theorem simplex_pos_eq_smul (m : ℕ) {a : ℝ} (ha : 0 < a) :
    simplex m a = (fun y : Fin m → ℝ => a • y) '' simplex m 1 := by
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

theorem volume_simplex_pos (m : ℕ) {a : ℝ} (ha : 0 < a) :
    volume (simplex m a) = ENNReal.ofReal (a ^ m) * volume (simplex m 1) := by
  rw [simplex_pos_eq_smul m ha]
  have he : (fun y : Fin m → ℝ => a • y) = AffineMap.homothety (0 : Fin m → ℝ) a := by
    funext y
    simp [AffineMap.homothety_apply]
  rw [he, Measure.addHaar_image_homothety]
  simp [abs_of_nonneg (pow_nonneg ha.le m)]

theorem volume_simplex_zero (m : ℕ) [NeZero m] : volume (simplex m 0) = 0 := by
  rw [simplex_zero]
  exact measure_singleton _

theorem volume_simplex_eq_clamped (m : ℕ) [NeZero m] (a : ℝ) :
    volume (simplex m a) = volume (simplex m (max 0 a)) := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
  · rw [simplex_empty_of_neg m (lt_of_not_ge ha), measure_empty,
      max_eq_left (le_of_not_ge ha), volume_simplex_zero]

theorem volume_simplex_nonneg (m : ℕ) [NeZero m] {a : ℝ} (ha : 0 ≤ a) :
    volume (simplex m a) = ENNReal.ofReal (a ^ m) * volume (simplex m 1) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [volume_simplex_zero, NeZero.ne m]
  · exact volume_simplex_pos m ha

/-- Overlap volume as a power of the truncated radius. The unit simplex volume
is kept symbolic because it cancels in several later entropy expressions. -/
theorem volume_simplex_overlap (m : ℕ) [NeZero m] (a b : ℝ) (z : Fin m → ℝ) :
    volume {x | x ∈ simplex m a ∧ x - z ∈ simplex m b} =
      ENNReal.ofReal (overlapRadius a b z ^ m) * volume (simplex m 1) := by
  rw [overlap_eq_translated_simplex]
  have he : (fun y => y + lowerCorner z) '' simplex m (rawRadius a b z) =
      (fun x => x + (-lowerCorner z)) ⁻¹' simplex m (rawRadius a b z) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + (-lowerCorner z), hx, by simp⟩
  rw [he, measure_preimage_add_right]
  rw [volume_simplex_eq_clamped m (rawRadius a b z)]
  exact volume_simplex_nonneg m (overlapRadius_nonneg a b z)

end EntropicRogersShephard

/-! ## Binomial -/

open Finset

namespace EntropicRogersShephard

/-- Finite binomial weights; no random-variable API is needed. -/
def binomialWeight (m : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j)

theorem binomialWeight_nonneg (m j : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binomialWeight m q j := by
  unfold binomialWeight
  positivity

theorem sum_binomialWeight (m : ℕ) (q : ℝ) :
    ∑ j ∈ range (m + 1), binomialWeight m q j = 1 := by
  have h := add_pow q (1 - q) m
  have he : q + (1 - q) = 1 := by ring
  rw [he, one_pow] at h
  calc
    _ = ∑ j ∈ range (m + 1), q ^ j * (1 - q) ^ (m - j) * (m.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold binomialWeight
      ring
    _ = 1 := h.symm

/-- Pascal's identity expressed as a recurrence for finite expectations. -/
theorem sum_binomialWeight_succ (m : ℕ) (q : ℝ) (F : ℕ → ℝ) :
    (∑ j ∈ range (m + 2), binomialWeight (m + 1) q j * F j) =
      (1 - q) * (∑ j ∈ range (m + 1), binomialWeight m q j * F j) +
      q * (∑ j ∈ range (m + 1), binomialWeight m q j * F (j + 1)) := by
  have h := Finset.sum_choose_succ_mul (fun i j => q ^ i * (1 - q) ^ j * F i) m
  calc
    _ = ∑ j ∈ range (m + 2), ((m + 1).choose j : ℝ) *
      (q ^ j * (1 - q) ^ (m + 1 - j) * F j) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold binomialWeight
      ring
    _ = _ := h
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hexp : m + 1 - j = (m - j) + 1 := by omega
        rw [hexp, pow_succ]
        unfold binomialWeight
        ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ]
        unfold binomialWeight
        ring

theorem sum_binomialWeight_mul_index (m : ℕ) (q : ℝ) :
    ∑ j ∈ range (m + 1), binomialWeight m q j * (j : ℝ) = (m : ℝ) * q := by
  induction m with
  | zero => simp [binomialWeight]
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 by omega, sum_binomialWeight_succ]
    have hshift :
        (∑ j ∈ range (m + 1), binomialWeight m q j * ((j + 1 : ℕ) : ℝ)) =
          (∑ j ∈ range (m + 1), binomialWeight m q j * (j : ℝ)) + 1 := by
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [Finset.sum_add_distrib, sum_binomialWeight]
    rw [hshift, ih]
    push_cast
    ring

theorem sum_binomialWeight_mul_factorialMoment (m : ℕ) (q : ℝ) :
    ∑ j ∈ range (m + 1), binomialWeight m q j * ((j : ℝ) * ((j : ℝ) - 1)) =
      (m : ℝ) * ((m : ℝ) - 1) * q ^ 2 := by
  induction m with
  | zero => simp [binomialWeight]
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 by omega, sum_binomialWeight_succ]
    have hshift :
        (∑ j ∈ range (m + 1), binomialWeight m q j *
          (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1))) =
        (∑ j ∈ range (m + 1), binomialWeight m q j * ((j : ℝ) * ((j : ℝ) - 1))) +
        2 * (∑ j ∈ range (m + 1), binomialWeight m q j * (j : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hshift, ih, sum_binomialWeight_mul_index]
    push_cast
    ring

end EntropicRogersShephard

/-! ## Vandermonde -/

open Finset

namespace EntropicRogersShephard

/-- The coefficient identity in the simplex overlap level-volume polynomial. -/
theorem sum_choose_sq_mul_choose (m j : ℕ) (hj : j ≤ m) :
    (∑ k ∈ range (m + 1), (m.choose k) ^ 2 * k.choose j) =
      m.choose j * (2 * m - j).choose m := by
  have hterm (k : ℕ) (hk : k ∈ range (m + 1)) :
      (m.choose k) ^ 2 * k.choose j =
        m.choose j * (m.choose k * (m - j).choose (m - k)) := by
    have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hjk : j ≤ k
    · have hmul := Nat.choose_mul (n := m) hjk
      have hkj : k - j ≤ m - j := by omega
      have hsub : m - j - (k - j) = m - k := by omega
      have hsym : (m - j).choose (k - j) = (m - j).choose (m - k) := by
        rw [← hsub]
        exact (Nat.choose_symm hkj).symm
      rw [hsym] at hmul
      calc
        _ = m.choose k * (m.choose k * k.choose j) := by ring
        _ = _ := by rw [hmul]; ring
    · have h₁ : k.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h₂ : (m - j).choose (m - k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h₁, h₂]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hv := Nat.add_choose_eq m (m - j) m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hi : m + (m - j) = 2 * m - j := by omega
  rw [hi] at hv
  rw [← hv]

end EntropicRogersShephard

/-! ## Harmonic -/

open Finset Real

namespace EntropicRogersShephard

def H (n : ℕ) : ℝ := (harmonic n : ℝ)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]

theorem H_succ (n : ℕ) : H (n + 1) = H n + 1 / ((n : ℝ) + 1) := by
  simp [H, harmonic_succ, one_div]

/-- The uniform quadratic bound needed in the scaled-simplex comparison. -/
theorem harmonic_drop_le (m j : ℕ) (hm : 0 < m) (hj : j ≤ m) :
    H (2 * m) - H (2 * m - j) ≤
      (j : ℝ) / (2 * (m : ℝ)) + (j : ℝ) * ((j : ℝ) - 1) / (4 * (m : ℝ) ^ 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjm : j ≤ m := by omega
    have hprev := ih hjm
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hjR : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
    have ht := harmonic_term_bound (m : ℝ) (j : ℝ) hmR (by positivity) hjR
    have hn : 2 * m - j = (2 * m - (j + 1)) + 1 := by omega
    have hden : ((2 * m - (j + 1) : ℕ) : ℝ) + 1 = 2 * (m : ℝ) - (j : ℝ) := by
      have he : (2 * m - (j + 1)) + (j + 1) = 2 * m := by omega
      have her : ((2 * m - (j + 1) : ℕ) : ℝ) + ((j : ℝ) + 1) = 2 * (m : ℝ) := by
        exact_mod_cast he
      linarith
    have hrec : H (2 * m - j) = H (2 * m - (j + 1)) +
        1 / (2 * (m : ℝ) - (j : ℝ)) := by
      rw [hn, H_succ, hden]
    have hpoly :
        ((j : ℝ) + 1) / (2 * (m : ℝ)) +
          ((j : ℝ) + 1) * (((j : ℝ) + 1) - 1) / (4 * (m : ℝ) ^ 2) =
        (j : ℝ) / (2 * (m : ℝ)) + (j : ℝ) * ((j : ℝ) - 1) / (4 * (m : ℝ) ^ 2) +
          (1 / (2 * (m : ℝ)) + (j : ℝ) / (2 * (m : ℝ) ^ 2)) := by ring
    push_cast
    rw [hpoly]
    linarith

theorem binomial_harmonic_drop_le (m : ℕ) (hm : 0 < m) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ j ∈ range (m + 1), binomialWeight m q j * (H (2 * m) - H (2 * m - j))) ≤
      q / 2 + ((m : ℝ) - 1) / (4 * (m : ℝ)) * q ^ 2 := by
  have hbound :
      (∑ j ∈ range (m + 1), binomialWeight m q j * (H (2 * m) - H (2 * m - j))) ≤
      ∑ j ∈ range (m + 1), binomialWeight m q j *
        ((j : ℝ) / (2 * (m : ℝ)) + (j : ℝ) * ((j : ℝ) - 1) / (4 * (m : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (harmonic_drop_le m j hm (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (binomialWeight_nonneg m j hq hq1)
  have he :
      (∑ j ∈ range (m + 1), binomialWeight m q j *
        ((j : ℝ) / (2 * (m : ℝ)) + (j : ℝ) * ((j : ℝ) - 1) / (4 * (m : ℝ) ^ 2))) =
        q / 2 + ((m : ℝ) - 1) / (4 * (m : ℝ)) * q ^ 2 := by
    have hsplit :
        (∑ j ∈ range (m + 1), binomialWeight m q j *
          ((j : ℝ) / (2 * (m : ℝ)) + (j : ℝ) * ((j : ℝ) - 1) / (4 * (m : ℝ) ^ 2))) =
        (∑ j ∈ range (m + 1), binomialWeight m q j * (j : ℝ)) / (2 * (m : ℝ)) +
        (∑ j ∈ range (m + 1), binomialWeight m q j * ((j : ℝ) * ((j : ℝ) - 1))) /
          (4 * (m : ℝ) ^ 2) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit, sum_binomialWeight_mul_index, sum_binomialWeight_mul_factorialMoment]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    field_simp
    <;> ring
  exact hbound.trans_eq he

/-- The finite algebraic core of the simplex entropy lower bound.
The remaining geometric work is to identify the entropy with this harmonic average. -/
theorem binomial_scale_gap_lower (m : ℕ) (hm : 0 < m) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    q ^ 2 / 4 ≤
      -(m : ℝ) / 2 * Real.log (1 - q) -
        (m : ℝ) * (∑ j ∈ range (m + 1),
          binomialWeight m q j * (H (2 * m) - H (2 * m - j))) := by
  have hdrop := binomial_harmonic_drop_le m hm hq hq1.le
  have hmR : 0 ≤ (m : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdrop hmR
  have hgap := scale_gap_lower (m : ℝ) q hmR hq hq1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have he : (m : ℝ) * (q / 2 + ((m : ℝ) - 1) / (4 * (m : ℝ)) * q ^ 2) =
      (m : ℝ) * q / 2 + ((m : ℝ) - 1) / 4 * q ^ 2 := by
    field_simp
  rw [he] at hmul
  nlinarith

end EntropicRogersShephard

/-! ## ScaleComparison -/

open Finset Real

namespace EntropicRogersShephard

theorem sum_binomialWeight_harmonic_drop (m : ℕ) (q : ℝ) :
    (∑ j ∈ range (m + 1), binomialWeight m q j * (H (2 * m) - H (2 * m - j))) =
      H (2 * m) - ∑ j ∈ range (m + 1), binomialWeight m q j * H (2 * m - j) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_binomialWeight, one_mul]

/-- The entropy-formula comparison for ordered positive scales.
This theorem concerns the explicit harmonic expression; identifying it with
the entropy of the simplex difference is a separate analytic theorem. -/
theorem harmonic_average_scale_bound (m : ℕ) (hm : 0 < m) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (m : ℝ) * H (2 * m) + (m : ℝ) / 2 * (Real.log a + Real.log b) ≤
      (m : ℝ) * Real.log a + (m : ℝ) *
        (∑ j ∈ range (m + 1), binomialWeight m (1 - b / a) j * H (2 * m - j)) := by
  have hratio0 : 0 < b / a := div_pos hb ha
  have hratio1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hq0 : 0 ≤ 1 - b / a := sub_nonneg.mpr hratio1
  have hq1 : 1 - b / a < 1 := by linarith
  have hg := binomial_scale_gap_lower m hm hq0 hq1
  rw [sum_binomialWeight_harmonic_drop] at hg
  have hlog : Real.log (1 - (1 - b / a)) = Real.log b - Real.log a := by
    rw [sub_sub_cancel, Real.log_div hb.ne' ha.ne']
  rw [hlog] at hg
  nlinarith [sq_nonneg (1 - b / a)]

theorem harmonic_average_scale_strict (m : ℕ) (hm : 0 < m) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (m : ℝ) * H (2 * m) + (m : ℝ) / 2 * (Real.log a + Real.log b) <
      (m : ℝ) * Real.log a + (m : ℝ) *
        (∑ j ∈ range (m + 1), binomialWeight m (1 - b / a) j * H (2 * m - j)) := by
  have hratio0 : 0 < b / a := div_pos hb ha
  have hratio1 : b / a < 1 := (div_lt_one ha).mpr hba
  have hq0 : 0 < 1 - b / a := sub_pos.mpr hratio1
  have hq1 : 1 - b / a < 1 := by linarith
  have hg := binomial_scale_gap_lower m hm hq0.le hq1
  rw [sum_binomialWeight_harmonic_drop] at hg
  have hlog : Real.log (1 - (1 - b / a)) = Real.log b - Real.log a := by
    rw [sub_sub_cancel, Real.log_div hb.ne' ha.ne']
  rw [hlog] at hg
  nlinarith [sq_pos_of_pos hq0]

end EntropicRogersShephard

/-! ## CoefficientLimit -/

open Real Finset Filter
open scoped Topology

namespace EntropicRogersShephard

def F (k : ℕ) : ℝ := (k : ℝ) * (H (2 * k) - H k)

theorem F_succ_sub (k : ℕ) :
    F (k + 1) - F k = H (2 * k) - H k + 1 / (2 * (2 * (k : ℝ) + 1)) := by
  have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  unfold F
  rw [h2, H_succ, H_succ, H_succ]
  push_cast
  field_simp
  <;> ring

theorem tendsto_harmonic_double_sub :
    Tendsto (fun k => H (2 * k) - H k) atTop (𝓝 (Real.log 2)) := by
  have ht : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => by change k ≤ 2 * k; omega) tendsto_id
  have h2 := Real.tendsto_harmonic_sub_log.comp ht
  have h1 := Real.tendsto_harmonic_sub_log
  have h := (h2.sub h1).add_const (Real.log 2)
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [Function.comp_apply, H, Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk0]
  ring

theorem tendsto_F_succ_sub :
    Tendsto (fun k => F (k + 1) - F k) atTop (𝓝 (Real.log 2)) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun k : ℕ => 2 * (2 * (k : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1
      (hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  have hinv : Tendsto (fun k : ℕ => 1 / (2 * (2 * (k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hden
  simpa only [F_succ_sub, add_zero] using tendsto_harmonic_double_sub.add hinv

/-- The exact coefficient limit needed after cancelling the simplex fibers. -/
theorem tendsto_F_shift_sub (n : ℕ) :
    Tendsto (fun m => F (m + n) - F m) atTop (𝓝 ((n : ℝ) * Real.log 2)) := by
  induction n with
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ n ih =>
    have hstep := tendsto_F_succ_sub.comp (tendsto_add_atTop_nat n)
    have h := ih.add hstep
    convert h using 1
    · funext m
      simp only [Function.comp_apply, Nat.add_assoc]
      ring
    · push_cast
      ring

end EntropicRogersShephard

/-! ## LogMoments -/

open Real MeasureTheory Set intervalIntegral

namespace EntropicRogersShephard

theorem intervalIntegrable_pow_mul_log (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ k * Real.log t) volume 0 1 := by
  exact (intervalIntegrable_log' : IntervalIntegrable Real.log volume 0 1).continuousOn_mul
    (by fun_prop)

theorem continuous_pow_succ_mul_log (k : ℕ) :
    Continuous (fun t : ℝ => t ^ (k + 1) * Real.log t) := by
  convert (continuous_pow k).mul Real.continuous_mul_log using 1
  funext t
  change t ^ (k + 1) * log t = t ^ k * (t * log t)
  ring

/-- Integer log moments, proved directly using a continuous primitive at zero. -/
theorem integral_pow_mul_log (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ k * Real.log t) = -1 / ((k : ℝ) + 1) ^ 2 := by
  let F : ℝ → ℝ := fun t => t ^ (k + 1) * Real.log t / ((k : ℝ) + 1) -
    t ^ (k + 1) / ((k : ℝ) + 1) ^ 2
  have hc : Continuous F := by
    exact ((continuous_pow_succ_mul_log k).div_const _).sub
      ((continuous_pow (k + 1)).div_const _)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (t ^ k * Real.log t) t := by
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have h := (((hasDerivAt_id t).pow (k + 1)).mul (Real.hasDerivAt_log ht0)).div_const
      ((k : ℝ) + 1)
    have h' := h.sub (((hasDerivAt_id t).pow (k + 1)).div_const (((k : ℝ) + 1) ^ 2))
    convert h' using 1
    <;> (try (funext x; rfl))
    <;> dsimp [F]
    <;> (try simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one])
    <;> field_simp
    <;> simp only [pow_succ]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hc.continuousOn hd (intervalIntegrable_pow_mul_log k)
  simpa [F, neg_div, one_div] using hi

theorem integral_pow_mul_neg_log (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ k * (-Real.log t)) = 1 / ((k : ℝ) + 1) ^ 2 := by
  simp_rw [mul_neg]
  rw [intervalIntegral.integral_neg, integral_pow_mul_log]
  ring

end EntropicRogersShephard

/-! ## BetaLog -/

open Real MeasureTheory intervalIntegral

namespace EntropicRogersShephard

noncomputable def integerBeta (a b : ℕ) : ℝ :=
  (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ)

theorem integerBeta_zero (a : ℕ) : integerBeta a 0 = 1 / ((a : ℝ) + 1) := by
  have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  simp only [integerBeta, Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  field_simp

theorem integerBeta_succ_right (a b : ℕ) :
    integerBeta a (b + 1) = integerBeta a b * ((b : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2) := by
  have hi : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
  unfold integerBeta
  rw [hi, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  <;> ring

theorem integerBeta_succ_left (a b : ℕ) :
    integerBeta (a + 1) b = integerBeta a b * ((a : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2) := by
  have hi : (a + 1) + b + 1 = (a + b + 1) + 1 := by omega
  unfold integerBeta
  rw [hi, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  <;> ring

noncomputable def betaMoment (a b : ℕ) : ℝ :=
  ∫ t : ℝ in 0..1, t ^ a * (1 - t) ^ b

theorem intervalIntegrable_betaMoment (a b : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ a * (1 - t) ^ b) volume 0 1 := by
  exact (by fun_prop : Continuous (fun t : ℝ => t ^ a * (1 - t) ^ b)).intervalIntegrable 0 1

theorem betaMoment_zero (a : ℕ) : betaMoment a 0 = 1 / ((a : ℝ) + 1) := by
  simp [betaMoment, integral_pow]

theorem betaMoment_succ (a b : ℕ) :
    betaMoment a (b + 1) = betaMoment a b - betaMoment (a + 1) b := by
  have he : (fun t : ℝ => t ^ a * (1 - t) ^ (b + 1)) =
      (fun t : ℝ => t ^ a * (1 - t) ^ b - t ^ (a + 1) * (1 - t) ^ b) := by
    funext t
    rw [pow_succ, pow_succ]
    ring
  unfold betaMoment
  rw [he, intervalIntegral.integral_sub
    (intervalIntegrable_betaMoment a b) (intervalIntegrable_betaMoment (a + 1) b)]

theorem betaMoment_eq_integerBeta (a b : ℕ) : betaMoment a b = integerBeta a b := by
  induction b generalizing a with
  | zero => rw [betaMoment_zero, integerBeta_zero]
  | succ b ih =>
    rw [betaMoment_succ, ih a, ih (a + 1), integerBeta_succ_right, integerBeta_succ_left]
    field_simp
    <;> ring

noncomputable def betaLogMoment (a b : ℕ) : ℝ :=
  ∫ t : ℝ in 0..1, t ^ a * (1 - t) ^ b * (-Real.log t)

theorem intervalIntegrable_betaLogMoment (a b : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ a * (1 - t) ^ b * (-Real.log t)) volume 0 1 := by
  exact (intervalIntegrable_log'.neg : IntervalIntegrable (fun t => -Real.log t) volume 0 1)
    |>.continuousOn_mul (by fun_prop)

theorem betaLogMoment_zero (a : ℕ) : betaLogMoment a 0 = 1 / ((a : ℝ) + 1) ^ 2 := by
  simpa [betaLogMoment] using integral_pow_mul_neg_log a

theorem betaLogMoment_succ (a b : ℕ) :
    betaLogMoment a (b + 1) = betaLogMoment a b - betaLogMoment (a + 1) b := by
  have he : (fun t : ℝ => t ^ a * (1 - t) ^ (b + 1) * (-Real.log t)) =
      (fun t : ℝ => t ^ a * (1 - t) ^ b * (-Real.log t) -
        t ^ (a + 1) * (1 - t) ^ b * (-Real.log t)) := by
    funext t
    rw [pow_succ, pow_succ]
    ring
  unfold betaLogMoment
  rw [he, intervalIntegral.integral_sub
    (intervalIntegrable_betaLogMoment a b) (intervalIntegrable_betaLogMoment (a + 1) b)]

/-- The integer Beta log-moment identity without parameter differentiation,
Gamma derivatives, or differentiation under the integral sign. -/
theorem betaLogMoment_eq_harmonic (a b : ℕ) :
    betaLogMoment a b = integerBeta a b * (H (a + b + 1) - H a) := by
  induction b generalizing a with
  | zero =>
    rw [betaLogMoment_zero, integerBeta_zero]
    simp only [Nat.add_zero, H_succ]
    field_simp
    <;> ring
  | succ b ih =>
    rw [betaLogMoment_succ, ih a, ih (a + 1), integerBeta_succ_right,
      integerBeta_succ_left]
    have hi₁ : (a + 1) + b + 1 = (a + b + 1) + 1 := by omega
    have hi₂ : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
    rw [hi₁, hi₂, H_succ (a + b + 1), H_succ a]
    push_cast
    field_simp
    <;> ring

end EntropicRogersShephard

/-! ## Entropy -/

open MeasureTheory Set Filter Real
open scoped Topology ENNReal

namespace EntropicRogersShephard

/-- Density entropy. Probability-density and finiteness conditions are stated in theorems. -/
noncomputable def differentialEntropy {α : Type*} [MeasurableSpace α]
    (f : α → ℝ) (μ : Measure α) : ℝ := ∫ x, Real.negMulLog (f x) ∂μ

theorem exists_negMulLog_bound (C : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) C, ‖Real.negMulLog t‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    Real.continuous_negMulLog.norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM ⟨t, ht, rfl⟩).trans (le_max_left _ _)

theorem integrable_negMulLog_of_bounded_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) C) (hsupp : ∀ x ∉ s, f x = 0) :
    Integrable (fun x => Real.negMulLog (f x)) μ := by
  obtain ⟨M, hM0, hM⟩ := exists_negMulLog_bound C
  have hint : Integrable (s.indicator (fun _ : α => M)) μ := by
    rw [integrable_indicator_iff hs]
    exact integrableOn_const hμs
  apply hint.mono' (Real.continuous_negMulLog.measurable.comp hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    exact hM _ (hb x)
  · simp [hx, hsupp x hx]

/-- Entropy convergence from pointwise convergence and a common bounded finite-measure support.
This allows the concave-power approximation without uniform-convergence machinery. -/
theorem entropy_tendsto_of_bounded_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, Measurable (f n)) {C : ℝ}
    (hb : ∀ n x, f n x ∈ Icc (0 : ℝ) C)
    (hsupp : ∀ n x, x ∉ s → f n x = 0)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => differentialEntropy (f n) μ) atTop (𝓝 (differentialEntropy g μ)) := by
  obtain ⟨M, hM0, hM⟩ := exists_negMulLog_bound C
  have hint : Integrable (s.indicator (fun _ : α => M)) μ := by
    rw [integrable_indicator_iff hs]
    exact integrableOn_const hμs
  apply tendsto_integral_of_dominated_convergence (s.indicator (fun _ : α => M))
    (fun n => (Real.continuous_negMulLog.measurable.comp (hf n)).aestronglyMeasurable) hint
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact hM _ (hb n x)
    · simp [hx, hsupp n x hx]
  · exact Filter.Eventually.of_forall fun x =>
      Real.continuous_negMulLog.continuousAt.tendsto.comp (hlim x)

/-- Concavity of density entropy under an explicitly integrable mixture.
No conditional entropy or disintegration is invoked. -/
theorem average_entropy_le_entropy_mixture {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [SFinite ν] {κ : α → β → ℝ}
    (hnonneg : ∀ b, ∀ᵐ a ∂μ, 0 ≤ κ a b)
    (hκ : ∀ b, Integrable (fun a => κ a b) μ)
    (hκlog : ∀ b, Integrable (fun a => Real.negMulLog (κ a b)) μ)
    (hprod : Integrable (fun p : α × β => Real.negMulLog (κ p.1 p.2)) (μ.prod ν))
    (hmix : Integrable (fun b => Real.negMulLog (∫ a, κ a b ∂μ)) ν) :
    (∫ a, differentialEntropy (κ a) ν ∂μ) ≤
      differentialEntropy (fun b => ∫ a, κ a b ∂μ) ν := by
  change (∫ a, ∫ b, Real.negMulLog (κ a b) ∂ν ∂μ) ≤
    ∫ b, Real.negMulLog (∫ a, κ a b ∂μ) ∂ν
  rw [integral_integral_swap hprod]
  apply integral_mono hprod.integral_prod_right hmix
  intro b
  exact Real.concaveOn_negMulLog.le_map_integral
    Real.continuous_negMulLog.continuousOn isClosed_Ici
    (hnonneg b) (hκ b) (hκlog b)

end EntropicRogersShephard

/-! ## Statement -/

open MeasureTheory

namespace EntropicRogersShephard

/-- Pointwise multiplicative log-concavity, including densities with zeros. -/
def IsLogConcave (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    Real.rpow (f x) a * Real.rpow (f y) b ≤ f (a • x + b • y)

def IsProbabilityDensity (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ (∫ x, f x) = 1

/-- The density of the difference of two independent vectors with density `f`. -/
noncomputable def differenceDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (s : Fin n → ℝ) : ℝ := ∫ x, f x * f (x - s)

/-- The full density-form target. Entropy integrability is a conclusion,
and is deliberately not included among the density assumptions.
This proposition has not yet been proved in this project. -/
def SharpEntropicRogersShephard : Prop :=
  ∀ n : ℕ, 0 < n → ∀ f : (Fin n → ℝ) → ℝ,
    IsProbabilityDensity n f → IsLogConcave n f →
    Integrable (fun x => Real.negMulLog (f x)) volume ∧
    Integrable (fun s => Real.negMulLog (differenceDensity f s)) volume ∧
    differentialEntropy (differenceDensity f) volume - differentialEntropy f volume ≤
      (n : ℝ) * Real.log 2

end EntropicRogersShephard

/-! ## PowerApproximation -/

open Real Filter
open scoped Topology

namespace EntropicRogersShephard

/-- Integer powers approximating the exponential, with a fixed initial dimension offset. -/
noncomputable def powerApproximation (M : ℕ) (v : ℝ) (n : ℕ) : ℝ :=
  (1 - v / ((n + M : ℕ) : ℝ)) ^ (n + M)

theorem powerApproximation_tendsto (M : ℕ) (v : ℝ) :
    Tendsto (powerApproximation M v) atTop (𝓝 (Real.exp (-v))) := by
  change Tendsto (fun n : ℕ => (1 - v / ((n + M : ℕ) : ℝ)) ^ (n + M)) atTop
    (𝓝 (Real.exp (-v)))
  simpa only [sub_eq_add_neg, neg_div, Function.comp_def] using
    (Real.tendsto_one_add_div_pow_exp (-v)).comp (tendsto_add_atTop_nat M)

theorem powerApproximation_mem_Icc (M n : ℕ) {v R : ℝ}
    (hv0 : 0 ≤ v) (hvR : v ≤ R) (hRM : R < (M : ℝ)) :
    powerApproximation M v n ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hM : 0 < (M : ℝ) := by linarith
  have hden : 0 < ((n + M : ℕ) : ℝ) := by push_cast; linarith
  have hvden : v < ((n + M : ℕ) : ℝ) := by push_cast; linarith
  have hbase0 : 0 ≤ 1 - v / ((n + M : ℕ) : ℝ) :=
    sub_nonneg.mpr ((div_le_one hden).mpr hvden.le)
  have hbase1 : 1 - v / ((n + M : ℕ) : ℝ) ≤ 1 :=
    sub_le_self _ (div_nonneg hv0 hden.le)
  exact ⟨pow_nonneg hbase0 _, pow_le_one₀ hbase0 hbase1⟩

theorem powerApproximation_pos (M n : ℕ) {v R : ℝ}
    (hv0 : 0 ≤ v) (hvR : v ≤ R) (hRM : R < (M : ℝ)) :
    0 < powerApproximation M v n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hM : 0 < (M : ℝ) := by linarith
  have hden : 0 < ((n + M : ℕ) : ℝ) := by push_cast; linarith
  have hvden : v < ((n + M : ℕ) : ℝ) := by push_cast; linarith
  exact pow_pos (sub_pos.mpr ((div_lt_one hden).mpr hvden)) _

end EntropicRogersShephard

/-! ## FiberBody -/

open Set Finset

namespace EntropicRogersShephard

def fiberBody (n m : ℕ) (K : Set (Fin n → ℝ)) (ρ : (Fin n → ℝ) → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) := {p | p.1 ∈ K ∧ p.2 ∈ simplex m (ρ p.1)}

/-- A concave simplex-size function produces a convex body in the product space. -/
theorem convex_fiberBody (n m : ℕ) (K : Set (Fin n → ℝ)) (ρ : (Fin n → ℝ) → ℝ)
    (hρ : ConcaveOn ℝ K ρ) : Convex ℝ (fiberBody n m K ρ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hρ.1 hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.2.1 i)) (mul_nonneg hb (hy.2.1 i))
  · change ∑ i, (a * x.2 i + b * y.2 i) ≤ ρ (a • x.1 + b • y.1)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x.2 i + b * ∑ i, y.2 i ≤ a * ρ x.1 + b * ρ y.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha) (mul_le_mul_of_nonneg_left hy.2.2 hb)
      _ ≤ ρ (a • x.1 + b • y.1) := hρ.2 hx.1 hy.1 ha hb hab

end EntropicRogersShephard

/-! ## BodyOverlap -/

open Set

namespace EntropicRogersShephard

def bodyOverlap {n : ℕ} (B : Set (Fin n → ℝ)) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ B ∧ x - z ∈ B}

@[simp] theorem bodyOverlap_zero {n : ℕ} (B : Set (Fin n → ℝ)) :
    bodyOverlap B 0 = B := by
  ext x
  simp [bodyOverlap]

theorem isCompact_bodyOverlap {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B)
    (z : Fin n → ℝ) : IsCompact (bodyOverlap B z) := by
  exact hB.inter_right (hB.isClosed.preimage (continuous_id.sub continuous_const))

theorem measurableSet_bodyOverlap {n : ℕ} {B : Set (Fin n → ℝ)} (hB : MeasurableSet B)
    (z : Fin n → ℝ) : MeasurableSet (bodyOverlap B z) := by
  exact hB.inter (hB.preimage (measurable_id.sub measurable_const))

/-- The geometric inclusion to which Brunn–Minkowski is applied. -/
theorem weighted_mem_bodyOverlap {n : ℕ} {B : Set (Fin n → ℝ)} (hB : Convex ℝ B)
    {z w x y : Fin n → ℝ} (hx : x ∈ bodyOverlap B z) (hy : y ∈ bodyOverlap B w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ bodyOverlap B (a • z + b • w) := by
  refine ⟨hB hx.1 hy.1 ha hb hab, ?_⟩
  have h := hB hx.2 hy.2 ha hb hab
  simpa only [smul_sub, sub_add_sub_comm] using h

end EntropicRogersShephard
