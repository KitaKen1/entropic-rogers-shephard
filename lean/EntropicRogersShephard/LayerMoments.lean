import EntropicRogersShephard.OrthantGeometry
import Mathlib.MeasureTheory.Integral.Layercake

/-! Layer-cake identities with the actual simplex overlap superlevels. -/

open MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem continuous_positiveMass (m : ℕ) : Continuous (positiveMass (m := m)) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).max continuous_const

theorem continuous_negativeMass (m : ℕ) : Continuous (negativeMass (m := m)) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).neg.max continuous_const

theorem continuous_overlapRadius (m : ℕ) (a b : ℝ) :
    Continuous (overlapRadius (m := m) a b) :=
  continuous_const.max ((continuous_const.sub (continuous_positiveMass m)).min
    (continuous_const.sub (continuous_negativeMass m)))

/-- Weighted layer cake for the overlap radius, with closed superlevels. -/
theorem overlapRadius_layercake (m : ℕ) (a b : ℝ) (g : ℝ → ℝ)
    (hgint : ∀ r > 0, IntervalIntegrable g volume 0 r)
    (hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (∫ t in 0..overlapRadius a b z, g t)) =
      ∫⁻ t in Ioi (0 : ℝ),
        volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} * ENNReal.ofReal (g t) :=
  lintegral_comp_eq_lintegral_meas_le_mul volume
    (Filter.Eventually.of_forall (overlapRadius_nonneg a b))
    (continuous_overlapRadius m a b).measurable.aemeasurable hgint hgnn

theorem overlapRadius_layer_integral_bounded (m : ℕ) (a : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (g : ℝ → ℝ) :
    (∫⁻ t in Ioi (0 : ℝ),
      volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} * ENNReal.ofReal (g t)) =
    ∫⁻ t in Ioc (0 : ℝ) b,
      volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} * ENNReal.ofReal (g t) := by
  let L : ℝ → ℝ≥0∞ := fun t =>
    volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} * ENNReal.ofReal (g t)
  have hsupp : Function.support ((Ioi (0 : ℝ)).indicator L) ⊆ Ioc 0 b := by
    intro t ht
    by_contra hn
    apply ht
    by_cases ht0 : 0 < t
    · have hbt : b < t := by
        by_contra h
        exact hn ⟨ht0, le_of_not_gt h⟩
      have he : {z : Fin m → ℝ | t ≤ overlapRadius a b z} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact (not_le_of_gt hbt) (hz.trans (overlapRadius_le_right a b z hb))
      simp [L, he]
    · simp [ht0]
  calc
    (∫⁻ t in Ioi (0 : ℝ), L t) = ∫⁻ t, (Ioi (0 : ℝ)).indicator L t :=
      (lintegral_indicator measurableSet_Ioi L).symm
    _ = ∫⁻ t in Ioc 0 b, (Ioi (0 : ℝ)).indicator L t :=
      (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ t in Ioc 0 b, L t := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact Set.indicator_of_mem ht.1 L

/-- The finite-interval identity includes the top level; the endpoint has zero
Lebesgue measure and is removed in the next theorem. -/
theorem overlapRadius_layercake_bounded (m : ℕ) (a : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (g : ℝ → ℝ) (hgint : ∀ r > 0, IntervalIntegrable g volume 0 r)
    (hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (∫ t in 0..overlapRadius a b z, g t)) =
      ∫⁻ t in Ioc (0 : ℝ) b,
        volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} * ENNReal.ofReal (g t) := by
  rw [overlapRadius_layercake m a b g hgint hgnn]
  exact overlapRadius_layer_integral_bounded m a hb g

/-- Weighted moment expressed entirely through the two coordinate-simplex blocks. -/
theorem overlapRadius_layercake_orthants (m : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (g : ℝ → ℝ) (hgint : ∀ r > 0, IntervalIntegrable g volume 0 r)
    (hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (∫ t in 0..overlapRadius a b z, g t)) =
      ∫⁻ t in Ioo (0 : ℝ) b,
        (∑ s : Finset (Fin m),
          (ENNReal.ofReal ((a - t) ^ Fintype.card {i : Fin m // i ∈ s}) *
            volume (simplexOn {i : Fin m // i ∈ s} 1)) *
          (ENNReal.ofReal ((b - t) ^ Fintype.card {i : Fin m // i ∉ s}) *
            volume (simplexOn {i : Fin m // i ∉ s} 1))) * ENNReal.ofReal (g t) := by
  rw [overlapRadius_layercake_bounded m a hb g hgint hgnn]
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc :
    Ioo (0 : ℝ) b =ᵐ[volume] Ioc (0 : ℝ) b)]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [volume_overlap_superlevel m ht.1 (ht.2.trans_le hba) ht.2]

theorem integral_pow_derivative (k : ℕ) (hk : 0 < k) (r : ℝ) :
    (∫ t in 0..r, (k : ℝ) * t ^ (k - 1)) = r ^ k := by
  have he : k - 1 + 1 = k := by omega
  have hc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast he
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [intervalIntegral.integral_const_mul, integral_pow, he, zero_pow hk.ne', sub_zero]
  rw [hc]
  field_simp

/-- All positive integer moments of the actual radius, without real-parameter differentiation. -/
theorem lintegral_overlapRadius_pow_orthants (m k : ℕ) (hk : 0 < k) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (overlapRadius a b z ^ k)) =
      ∫⁻ t in Ioo (0 : ℝ) b,
        (∑ s : Finset (Fin m),
          (ENNReal.ofReal ((a - t) ^ Fintype.card {i : Fin m // i ∈ s}) *
            volume (simplexOn {i : Fin m // i ∈ s} 1)) *
          (ENNReal.ofReal ((b - t) ^ Fintype.card {i : Fin m // i ∉ s}) *
            volume (simplexOn {i : Fin m // i ∉ s} 1))) *
          ENNReal.ofReal ((k : ℝ) * t ^ (k - 1)) := by
  have hgint : ∀ r > 0, IntervalIntegrable (fun t : ℝ => (k : ℝ) * t ^ (k - 1)) volume 0 r := by
    intro r _
    exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  have hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ (k : ℝ) * t ^ (k - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Nat.cast_nonneg k) (pow_nonneg ht.le _)
  simpa only [integral_pow_derivative k hk] using
    overlapRadius_layercake_orthants m hb hba (fun t : ℝ => (k : ℝ) * t ^ (k - 1)) hgint hgnn

end EntropicRogersShephard
