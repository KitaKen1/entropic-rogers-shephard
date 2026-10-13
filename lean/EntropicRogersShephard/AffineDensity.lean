import EntropicRogersShephard.AffineVolume

/-! Invertible affine transport of actual densities and difference convolutions. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => affineJacobian A * f (A.symm (x - b))

theorem measurable_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (affineDensity A b f) := by
  unfold affineDensity
  fun_prop

theorem affineDensity_nonneg {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Fin n → ℝ) :
    0 ≤ affineDensity A b f x := mul_nonneg (affineJacobian_pos A).le (hf _)

theorem integrable_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) :
    Integrable (affineDensity A b f) volume :=
  (integrable_affine_inverse A b hf).const_mul _

theorem integral_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, affineDensity A b f x) = ∫ x, f x := by
  change (∫ x, affineJacobian A * f (A.symm (x - b))) = _
  rw [integral_const_mul, integral_affine_inverse, ← mul_assoc,
    mul_inv_cancel₀ (affineJacobian_pos A).ne', one_mul]

theorem isProbabilityDensity_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) :
    IsProbabilityDensity n (affineDensity A b f) :=
  ⟨measurable_affineDensity A b hf.1, affineDensity_nonneg A b hf.2.1,
    integrable_affineDensity A b hf.2.2.1, (integral_affineDensity A b f).trans hf.2.2.2⟩

theorem affine_inverse_combo {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b x y : Fin n → ℝ) {u v : ℝ} (huv : u + v = 1) :
    A.symm ((u • x + v • y) - b) = u • A.symm (x - b) + v • A.symm (y - b) := by
  have hv : v = 1 - u := by linarith
  have he : (u • x + v • y) - b = u • (x - b) + v • (y - b) := by
    ext i
    change u * x i + v * y i - b i = u * (x i - b i) + v * (y i - b i)
    rw [hv]
    ring
  rw [he, map_add, map_smul, map_smul]

theorem isLogConcave_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ} (hn : ∀ x, 0 ≤ f x) (hl : IsLogConcave n f) :
    IsLogConcave n (affineDensity A b f) := by
  intro x y u v hu hv huv
  let J := affineJacobian A
  have hJ : 0 < J := affineJacobian_pos A
  change Real.rpow (J * f (A.symm (x - b))) u * Real.rpow (J * f (A.symm (y - b))) v ≤
    J * f (A.symm ((u • x + v • y) - b))
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow hJ.le (hn _), Real.mul_rpow hJ.le (hn _)]
  calc
    (J ^ u * f (A.symm (x - b)) ^ u) * (J ^ v * f (A.symm (y - b)) ^ v) =
        (J ^ u * J ^ v) * (f (A.symm (x - b)) ^ u * f (A.symm (y - b)) ^ v) := by ring
    _ = J * (f (A.symm (x - b)) ^ u * f (A.symm (y - b)) ^ v) := by
      rw [← Real.rpow_add hJ, huv, Real.rpow_one]
    _ ≤ J * f (u • A.symm (x - b) + v • A.symm (y - b)) :=
      mul_le_mul_of_nonneg_left (hl _ _ u v hu hv huv) hJ.le
    _ = J * f (A.symm ((u • x + v • y) - b)) := by rw [affine_inverse_combo A b x y huv]

theorem affine_inverse_difference {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b x s : Fin n → ℝ) :
    A.symm ((x - s) - b) = A.symm (x - b) - A.symm s := by
  rw [show (x - s) - b = (x - b) - s by abel, map_sub]

theorem differenceDensity_affineDensity {n : ℕ} (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    differenceDensity (affineDensity A b f) = affineDensity A 0 (differenceDensity f) := by
  funext s
  let J := affineJacobian A
  have hJ : J ≠ 0 := (affineJacobian_pos A).ne'
  have hp (x : Fin n → ℝ) : affineDensity A b f x * affineDensity A b f (x - s) =
      J ^ 2 * (f (A.symm (x - b)) * f (A.symm (x - b) - A.symm s)) := by
    change (J * f (A.symm (x - b))) * (J * f (A.symm ((x - s) - b))) = _
    rw [affine_inverse_difference]
    ring
  change (∫ x, affineDensity A b f x * affineDensity A b f (x - s)) =
    J * differenceDensity f (A.symm (s - 0))
  simp_rw [hp]
  have he : (fun x => f (A.symm (x - b)) * f (A.symm (x - b) - A.symm s)) =
      (fun x => (fun y => f y * f (y - A.symm s)) (A.symm (x - b))) := rfl
  rw [integral_const_mul, he, integral_affine_inverse A b (fun y => f y * f (y - A.symm s))]
  have hc : J ^ 2 * (affineJacobian A)⁻¹ = J := by
    change J ^ 2 * J⁻¹ = J
    field_simp [hJ]
  rw [← mul_assoc, hc, sub_zero]
  rfl

end EntropicRogersShephard
