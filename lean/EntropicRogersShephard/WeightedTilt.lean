import EntropicRogersShephard.MonotoneTilt

/-! Weighted mean comparison using ordinary integrals under the original measure. -/

open MeasureTheory Set

namespace EntropicRogersShephard

theorem weighted_integral_pair_difference {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {r l w : α → ℝ}
    (hw : Integrable w μ) (hrw : Integrable (fun x => r x * w x) μ)
    (hlw : Integrable (fun x => l x * w x) μ)
    (hrlw : Integrable (fun x => r x * l x * w x) μ) (x : α) :
    (∫ y, (r x - r y) * (l x - l y) * (w x * w y) ∂μ) =
      (∫ y, w y ∂μ) * (r x * l x * w x) -
        (∫ y, l y * w y ∂μ) * (r x * w x) -
        (∫ y, r y * w y ∂μ) * (l x * w x) +
        (∫ y, r y * l y * w y ∂μ) * w x := by
  have he : (fun y => (r x - r y) * (l x - l y) * (w x * w y)) =
      (fun y => (w x * r x * l x) * w y -
        (w x * r x) * (l y * w y) - (w x * l x) * (r y * w y) +
        w x * (r y * l y * w y)) := by
    funext y
    ring
  have h1 := hw.const_mul (w x * r x * l x)
  have h2 := hlw.const_mul (w x * r x)
  have h3 := hrw.const_mul (w x * l x)
  have h4 := hrlw.const_mul (w x)
  rw [he, integral_add
    (f := fun y => (w x * r x * l x) * w y -
      (w x * r x) * (l y * w y) - (w x * l x) * (r y * w y))
    (g := fun y => w x * (r y * l y * w y)) ((h1.sub h2).sub h3) h4,
    integral_sub (f := fun y => (w x * r x * l x) * w y -
      (w x * r x) * (l y * w y)) (g := fun y => (w x * l x) * (r y * w y))
      (h1.sub h2) h3,
    integral_sub (f := fun y => (w x * r x * l x) * w y)
      (g := fun y => (w x * r x) * (l y * w y)) h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem weighted_integral_mul_le_product_of_pair_nonpos {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {r l w : α → ℝ}
    (hw : Integrable w μ) (hrw : Integrable (fun x => r x * w x) μ)
    (hlw : Integrable (fun x => l x * w x) μ)
    (hrlw : Integrable (fun x => r x * l x * w x) μ)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (r x - r y) * (l x - l y) * (w x * w y) ≤ 0) :
    (∫ x, w x ∂μ) * (∫ x, r x * l x * w x ∂μ) ≤
      (∫ x, r x * w x ∂μ) * (∫ x, l x * w x ∂μ) := by
  have hnn : ∀ᵐ x ∂μ,
      (∫ y, w y ∂μ) * (r x * l x * w x) -
        (∫ y, l y * w y ∂μ) * (r x * w x) -
        (∫ y, r y * w y ∂μ) * (l x * w x) +
        (∫ y, r y * l y * w y ∂μ) * w x ≤ 0 := by
    filter_upwards [hpair] with x hx
    rw [← weighted_integral_pair_difference hw hrw hlw hrlw x]
    exact integral_nonpos_of_ae hx
  have h := integral_nonpos_of_ae hnn
  rw [integral_add
    (f := fun x => (∫ y, w y ∂μ) * (r x * l x * w x) -
      (∫ y, l y * w y ∂μ) * (r x * w x) - (∫ y, r y * w y ∂μ) * (l x * w x))
    (g := fun x => (∫ y, r y * l y * w y ∂μ) * w x)
    (((hrlw.const_mul _).sub (hrw.const_mul _)).sub (hlw.const_mul _)) (hw.const_mul _),
    integral_sub
      (f := fun x => (∫ y, w y ∂μ) * (r x * l x * w x) -
        (∫ y, l y * w y ∂μ) * (r x * w x))
      (g := fun x => (∫ y, r y * w y ∂μ) * (l x * w x))
      ((hrlw.const_mul _).sub (hrw.const_mul _)) (hlw.const_mul _),
    integral_sub
      (f := fun x => (∫ y, w y ∂μ) * (r x * l x * w x))
      (g := fun x => (∫ y, l y * w y ∂μ) * (r x * w x))
      (hrlw.const_mul _) (hrw.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at h
  nlinarith

theorem weighted_integral_mul_le_product_of_monotone_antitone {α : Type*} [LinearOrder α]
    [MeasurableSpace α] {μ : Measure α} {S : Set α} {r l w : α → ℝ}
    (hS : ∀ᵐ x ∂μ, x ∈ S) (hwnn : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw : Integrable w μ) (hrw : Integrable (fun x => r x * w x) μ)
    (hlw : Integrable (fun x => l x * w x) μ)
    (hrlw : Integrable (fun x => r x * l x * w x) μ)
    (hrmono : MonotoneOn r S) (hlanti : AntitoneOn l S) :
    (∫ x, w x ∂μ) * (∫ x, r x * l x * w x ∂μ) ≤
      (∫ x, r x * w x ∂μ) * (∫ x, l x * w x ∂μ) := by
  apply weighted_integral_mul_le_product_of_pair_nonpos hw hrw hlw hrlw
  filter_upwards [hS, hwnn] with x hx hwx
  filter_upwards [hS, hwnn] with y hy hwy
  have hpair : (r x - r y) * (l x - l y) ≤ 0 := by
    rcases le_total x y with hxy | hyx
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hrmono hx hy hxy))
        (sub_nonneg.mpr (hlanti hx hy hxy))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hrmono hy hx hyx))
        (sub_nonpos.mpr (hlanti hy hx hyx))
  exact mul_nonpos_of_nonpos_of_nonneg hpair (mul_nonneg hwx hwy)

end EntropicRogersShephard
