import EntropicRogersShephard.Density

/-! Oppositely ordered factors have nonpositive covariance.
The proof uses two one-variable integrations, without a joint L2 theory. -/

open MeasureTheory Set

namespace EntropicRogersShephard

theorem integral_pair_difference {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {r l : α → ℝ}
    (hr : Integrable r μ) (hl : Integrable l μ)
    (hrl : Integrable (fun y => r y * l y) μ) (x : α) :
    (∫ y, (r x - r y) * (l x - l y) ∂μ) =
      r x * l x - (∫ y, l y ∂μ) * r x - (∫ y, r y ∂μ) * l x +
        ∫ y, r y * l y ∂μ := by
  have he : (fun y => (r x - r y) * (l x - l y)) =
      (fun y => (r x * l x - r x * l y - l x * r y) + r y * l y) := by
    funext y
    ring
  have hc : Integrable (fun _ : α => r x * l x) μ := integrable_const _
  have hli := hl.const_mul (r x)
  have hri := hr.const_mul (l x)
  rw [he, integral_add
    (f := fun y => r x * l x - r x * l y - l x * r y)
    (g := fun y => r y * l y) ((hc.sub hli).sub hri) hrl,
    integral_sub (f := fun y => r x * l x - r x * l y)
      (g := fun y => l x * r y) (hc.sub hli) hri,
    integral_sub (f := fun _ : α => r x * l x) (g := fun y => r x * l y) hc hli,
    integral_const, integral_const_mul, integral_const_mul]
  simp only [probReal_univ, one_smul]
  ring

theorem integral_mul_le_product_of_pair_nonpos {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {r l : α → ℝ}
    (hr : Integrable r μ) (hl : Integrable l μ)
    (hrl : Integrable (fun x => r x * l x) μ)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (r x - r y) * (l x - l y) ≤ 0) :
    (∫ x, r x * l x ∂μ) ≤ (∫ x, r x ∂μ) * (∫ x, l x ∂μ) := by
  have hnn : ∀ᵐ x ∂μ, r x * l x - (∫ y, l y ∂μ) * r x -
      (∫ y, r y ∂μ) * l x + (∫ y, r y * l y ∂μ) ≤ 0 := by
    filter_upwards [hpair] with x hx
    rw [← integral_pair_difference hr hl hrl x]
    exact integral_nonpos_of_ae hx
  have h := integral_nonpos_of_ae hnn
  rw [integral_add
    (f := fun x => r x * l x - (∫ y, l y ∂μ) * r x - (∫ y, r y ∂μ) * l x)
    (g := fun _ : α => ∫ y, r y * l y ∂μ)
    ((hrl.sub (hr.const_mul _)).sub (hl.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => r x * l x - (∫ y, l y ∂μ) * r x)
      (g := fun x => (∫ y, r y ∂μ) * l x) (hrl.sub (hr.const_mul _)) (hl.const_mul _),
    integral_sub (f := fun x => r x * l x) (g := fun x => (∫ y, l y ∂μ) * r x)
      hrl (hr.const_mul _), integral_const_mul, integral_const_mul,
    integral_const] at h
  simp only [probReal_univ, one_smul] at h
  nlinarith

/-- A nonnegative increasing tilt lowers the mean of a decreasing observable.
The covariance form itself does not need a sign assumption on the tilt. -/
theorem integral_mul_le_product_of_monotone_antitone {α : Type*} [LinearOrder α]
    [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S : Set α} {r l : α → ℝ} (hS : ∀ᵐ x ∂μ, x ∈ S)
    (hr : Integrable r μ) (hl : Integrable l μ)
    (hrl : Integrable (fun x => r x * l x) μ)
    (hrmono : MonotoneOn r S) (hlanti : AntitoneOn l S) :
    (∫ x, r x * l x ∂μ) ≤ (∫ x, r x ∂μ) * (∫ x, l x ∂μ) := by
  apply integral_mul_le_product_of_pair_nonpos hr hl hrl
  filter_upwards [hS] with x hx
  filter_upwards [hS] with y hy
  rcases le_total x y with hxy | hyx
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hrmono hx hy hxy))
      (sub_nonneg.mpr (hlanti hx hy hxy))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hrmono hy hx hyx))
      (sub_nonpos.mpr (hlanti hy hx hyx))

end EntropicRogersShephard
