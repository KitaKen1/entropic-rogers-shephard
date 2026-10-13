import EntropicRogersShephard.ExponentialConvergence

/-! Almost-everywhere input convergence suffices at every difference shift. -/

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace EntropicRogersShephard

theorem differenceDensity_tendsto_of_dominated {n : ℕ}
    {f : ℕ → (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ} {B M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hg : IsProbabilityDensity n g)
    (hm : ∀ j, Measurable (f j)) (hf : ∀ j x, 0 ≤ f j x)
    (hdom : ∀ j x, f j x ≤ B * g x) (hb : ∀ x, g x ≤ M)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (s : Fin n → ℝ) :
    Tendsto (fun j => differenceDensity (f j) s) atTop (𝓝 (differenceDensity g s)) := by
  have hi := hg.2.2.1.const_mul (B ^ 2 * M)
  apply tendsto_integral_of_dominated_convergence (fun x => (B ^ 2 * M) * g x)
    (fun j => ((hm j).mul ((hm j).comp (measurable_id.sub measurable_const))).aestronglyMeasurable) hi
  · intro j
    apply Filter.Eventually.of_forall
    intro x
    change ‖f j x * f j (x - s)‖ ≤ (B ^ 2 * M) * g x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf j x) (hf j (x - s)))]
    calc
      f j x * f j (x - s) ≤ (B * g x) * (B * g (x - s)) :=
        mul_le_mul (hdom j x) (hdom j (x - s)) (hf j _) (mul_nonneg hB (hg.2.1 _))
      _ ≤ (B * g x) * (B * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb _) hB)
          (mul_nonneg hB (hg.2.1 _))
      _ = (B ^ 2 * M) * g x := by ring
  · have ht : ∀ᵐ x ∂volume, Tendsto (fun j => f j (x - s)) atTop (𝓝 (g (x - s))) := by
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae hlim
    filter_upwards [hlim, ht] with x hx hxs
    exact hx.mul hxs

end EntropicRogersShephard
