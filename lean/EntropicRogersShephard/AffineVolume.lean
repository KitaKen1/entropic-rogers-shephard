import EntropicRogersShephard.ProbabilityLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Change of variables for an invertible affine map, using its inverse determinant. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def affineJacobian {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : ℝ :=
  |LinearMap.det (A.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))|

theorem affineJacobian_pos {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    0 < affineJacobian A := by
  apply abs_pos.mpr
  exact (LinearEquiv.isUnit_det' A.symm.toLinearEquiv).ne_zero

theorem map_affine_inverse_linear_volume {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    volume.map (fun x => A.symm x) = ENNReal.ofReal ((affineJacobian A)⁻¹) • volume := by
  have hdet : LinearMap.det (A.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' A.symm.toLinearEquiv).ne_zero
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  change volume.map (fun x => A.symm x) =
    ENNReal.ofReal |(LinearMap.det (A.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))⁻¹| • volume at h
  simpa only [affineJacobian, abs_inv] using h

theorem integral_affine_inverse {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (h : (Fin n → ℝ) → ℝ) :
    (∫ x, h (A.symm (x - b))) = (affineJacobian A)⁻¹ * ∫ x, h x := by
  have he : MeasurableEmbedding (fun x => A.symm x) := A.symm.toHomeomorph.measurableEmbedding
  have hJ := affineJacobian_pos A
  rw [integral_sub_right_eq_self (fun x => h (A.symm x)) b,
    ← he.integral_map h, map_affine_inverse_linear_volume,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hJ.le), smul_eq_mul]

theorem integrable_affine_inverse {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {h : (Fin n → ℝ) → ℝ} (hh : Integrable h volume) :
    Integrable (fun x => h (A.symm (x - b))) volume := by
  have he : MeasurableEmbedding (fun x => A.symm x) := A.symm.toHomeomorph.measurableEmbedding
  have hm : Integrable h (volume.map (fun x => A.symm x)) := by
    rw [map_affine_inverse_linear_volume]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  have hi : Integrable (fun x => h (A.symm x)) volume := by
    simpa only [Function.comp_def] using he.integrable_map_iff.mp hm
  exact hi.comp_sub_right b

theorem lintegral_affine_inverse {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (h : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ x, h (A.symm (x - b))) = ENNReal.ofReal ((affineJacobian A)⁻¹) * ∫⁻ x, h x := by
  have he : MeasurableEmbedding (fun x => A.symm x) := A.symm.toHomeomorph.measurableEmbedding
  rw [lintegral_sub_right_eq_self (fun x => h (A.symm x)) b,
    ← he.lintegral_map h, map_affine_inverse_linear_volume, lintegral_smul_measure]
  rfl

end EntropicRogersShephard
