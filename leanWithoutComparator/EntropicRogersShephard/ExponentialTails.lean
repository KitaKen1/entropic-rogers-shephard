import EntropicRogersShephard.GlobalDensityBound

/-! A bounded positive superlevel gives an exponential envelope along rays. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

theorem logconcave_ray_log_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hl : IsLogConcave n f) {x y : Fin n → ℝ} (hx : 0 < f x) (hy : 0 < f y)
    {R : ℝ} (hR : 0 ≤ R) (hlevel : ∀ z, f x / 2 ≤ f z → dist z x ≤ R)
    (hfar : R + 1 ≤ dist y x) :
    Real.log (f y) ≤ Real.log (f x) - (Real.log 2 / (R + 1)) * dist y x := by
  let d := dist y x
  let L := R + 1
  have hL : 0 < L := by dsimp [L]; linarith
  have hd : 0 < d := hL.trans_le hfar
  let θ := L / d
  have hθ : 0 < θ := div_pos hL hd
  have hθ1 : θ ≤ 1 := (div_le_one hd).mpr hfar
  let z := (1 - θ) • x + θ • y
  have hzsub : z - x = θ • (y - x) := by
    ext i
    change (1 - θ) * x i + θ * y i - x i = θ * (y i - x i)
    ring
  have hzd : dist z x = L := by
    rw [dist_eq_norm, hzsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.le, ← dist_eq_norm]
    dsimp [θ, d]
    exact div_mul_cancel₀ _ hd.ne'
  have hzpos : 0 < f z := (convex_positiveSet_of_isLogConcave hl) hx hy
    (sub_nonneg.mpr hθ1) hθ.le (by ring)
  have hzu : f z < f x / 2 := by
    apply lt_of_not_ge
    intro h
    have hzR := hlevel z h
    rw [hzd] at hzR
    dsimp [L] at hzR
    linarith
  have hlogu : Real.log (f z) < Real.log (f x) - Real.log 2 := by
    have h := Real.log_lt_log hzpos hzu
    rwa [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hlog : (1 - θ) * Real.log (f x) + θ * Real.log (f y) ≤ Real.log (f z) := by
    simpa only [smul_eq_mul] using (concaveOn_log_of_isLogConcave hl).2 hx hy
      (sub_nonneg.mpr hθ1) hθ.le (by ring)
  have hθlog : θ * (Real.log (f y) - Real.log (f x)) ≤ -Real.log 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hθlog hd.le
  have hdt : d * θ = L := by dsimp [θ]; field_simp [hd.ne']
  rw [← mul_assoc, hdt] at hmul
  have hdiv := div_le_div_of_nonneg_right hmul hL.le
  have hel (a : ℝ) : L * a / L = a := mul_div_cancel_left₀ a hL.ne'
  rw [hel] at hdiv
  have her : d * (-Real.log 2) / L = -(Real.log 2 / L) * d := by ring
  rw [her] at hdiv
  change Real.log (f y) ≤ Real.log (f x) - (Real.log 2 / L) * d
  linarith

theorem logconcave_probability_density_exponential_envelope {n : ℕ} [NeZero n]
    {f : (Fin n → ℝ) → ℝ} (hf : IsProbabilityDensity n f) (hl : IsLogConcave n f) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ y, f y ≤ C * Real.exp (-a * ‖y‖) := by
  obtain ⟨x, hx, r, hr, hball⟩ := exists_density_anchor_ball hf hl
  have hfx : 0 < f x := interior_subset (s := {x | 0 < f x}) hx
  have ht : 0 < f x / 2 := by positivity
  have hAb := logconcave_superlevel_isBounded hf hl ht hr hball
  obtain ⟨R, hlevel⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hAb
  have hxlevel : f x / 2 ≤ f x := by linarith
  have hR : 0 ≤ R := by simpa only [Metric.mem_closedBall, dist_self] using hlevel hxlevel
  have hlevel' : ∀ z, f x / 2 ≤ f z → dist z x ≤ R := fun z hz => hlevel hz
  obtain ⟨M, hM, hMb⟩ := logconcave_probability_density_bounded hf hl
  let L := R + 1
  have hL : 0 < L := by dsimp [L]; linarith
  let a := Real.log 2 / L
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) hL
  let C := M * Real.exp (a * (L + ‖x‖))
  refine ⟨a, C, ha, mul_pos hM (Real.exp_pos _), ?_⟩
  intro y
  have hnorm : ‖y‖ ≤ dist y x + ‖x‖ := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ = dist y x + ‖x‖ := by rw [dist_eq_norm]
  have hfactor : M * Real.exp (a * (L + ‖x‖) - a * ‖y‖) = C * Real.exp (-a * ‖y‖) := by
    dsimp [C]
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  by_cases hfar : L ≤ dist y x
  · by_cases hy : 0 < f y
    · have hlog := logconcave_ray_log_bound hl hfx hy hR hlevel' hfar
      have hdecay : f y ≤ f x * Real.exp (-a * dist y x) := by
        calc
          f y = Real.exp (Real.log (f y)) := (Real.exp_log hy).symm
          _ ≤ Real.exp (Real.log (f x) - a * dist y x) := Real.exp_le_exp.mpr hlog
          _ = f x * Real.exp (-a * dist y x) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hfx]
            congr 2
            ring
      calc
        f y ≤ f x * Real.exp (-a * dist y x) := hdecay
        _ ≤ M * Real.exp (-a * dist y x) := mul_le_mul_of_nonneg_right (hMb x).2 (Real.exp_pos _).le
        _ ≤ M * Real.exp (a * (L + ‖x‖) - a * ‖y‖) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hM.le
        _ = C * Real.exp (-a * ‖y‖) := hfactor
    · have hy0 : f y = 0 := le_antisymm (not_lt.mp hy) (hf.2.1 y)
      rw [hy0]
      exact mul_nonneg (mul_pos hM (Real.exp_pos _)).le (Real.exp_pos _).le
  · have hexp : 1 ≤ Real.exp (a * (L + ‖x‖) - a * ‖y‖) := Real.one_le_exp_iff.mpr (by
      have hd : dist y x < L := lt_of_not_ge hfar
      nlinarith)
    calc
      f y ≤ M := (hMb y).2
      _ ≤ M * Real.exp (a * (L + ‖x‖) - a * ‖y‖) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hM.le
      _ = C * Real.exp (-a * ‖y‖) := hfactor

end EntropicRogersShephard
