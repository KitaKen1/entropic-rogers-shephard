import EntropicRogersShephard.LayerMoments

/-! Real polynomial moments forced by normalization of the actual difference density. -/

open MeasureTheory Set Finset
open scoped ENNReal

namespace EntropicRogersShephard

theorem isCompact_simplexOn (ι : Type*) [Fintype ι] (a : ℝ) :
    IsCompact (simplexOn ι a) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ))
    (b := fun _ => a)) (isClosed_simplexOn ι a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro i
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

theorem volume_simplexOn_ne_top (ι : Type*) [Fintype ι] (a : ℝ) :
    volume (simplexOn ι a) ≠ ∞ := (isCompact_simplexOn ι a).measure_ne_top

noncomputable def orthantVolumePolynomial (m : ℕ) (a b t : ℝ) : ℝ :=
  ∑ s : Finset (Fin m),
    ((a - t) ^ Fintype.card {i : Fin m // i ∈ s} *
      (volume (simplexOn {i : Fin m // i ∈ s} 1)).toReal) *
    ((b - t) ^ Fintype.card {i : Fin m // i ∉ s} *
      (volume (simplexOn {i : Fin m // i ∉ s} 1)).toReal)

theorem orthantVolumePolynomial_nonneg (m : ℕ) {a b t : ℝ}
    (hta : t ≤ a) (htb : t ≤ b) : 0 ≤ orthantVolumePolynomial m a b t := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr hta) _) ENNReal.toReal_nonneg)
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr htb) _) ENNReal.toReal_nonneg)

theorem continuous_orthantVolumePolynomial (m : ℕ) (a b : ℝ) :
    Continuous (orthantVolumePolynomial m a b) := by
  apply continuous_finsetSum
  intro s _
  exact (((continuous_const.sub continuous_id).pow _).mul continuous_const).mul
    (((continuous_const.sub continuous_id).pow _).mul continuous_const)

theorem volume_overlap_superlevel_eq_ofReal_polynomial (m : ℕ) {a b t : ℝ}
    (ht : 0 < t) (hta : t < a) (htb : t < b) :
    volume {z : Fin m → ℝ | t ≤ overlapRadius a b z} =
      ENNReal.ofReal (orthantVolumePolynomial m a b t) := by
  rw [volume_overlap_superlevel m ht hta htb]
  symm
  have hu : 0 ≤ a - t := sub_nonneg.mpr hta.le
  have hv : 0 ≤ b - t := sub_nonneg.mpr htb.le
  rw [orthantVolumePolynomial, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro s _
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (pow_nonneg hu _), ENNReal.ofReal_mul (pow_nonneg hv _),
      ENNReal.ofReal_toReal (volume_simplexOn_ne_top _ 1),
      ENNReal.ofReal_toReal (volume_simplexOn_ne_top _ 1)]
  · intro s _
    positivity

theorem volume_overlap_superlevel_real (m : ℕ) {a b t : ℝ}
    (ht : 0 < t) (hta : t < a) (htb : t < b) :
    (volume {z : Fin m → ℝ | t ≤ overlapRadius a b z}).toReal =
      orthantVolumePolynomial m a b t := by
  rw [volume_overlap_superlevel_eq_ofReal_polynomial m ht hta htb,
    ENNReal.toReal_ofReal (orthantVolumePolynomial_nonneg m hta.le htb.le)]

/-- The m-th radius moment follows from the already proved density normalization. -/
theorem lintegral_overlapRadius_pow_normalization (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (overlapRadius a b z ^ m)) =
      ENNReal.ofReal (a ^ m * b ^ m * (volume (simplex m 1)).toReal) := by
  let D : ℝ := a ^ m * b ^ m * (volume (simplex m 1)).toReal
  let d := crossDifferenceDensity (uniformDensity (simplex m a))
    (uniformDensity (simplex m b))
  have hd := isProbabilityDensity_crossDifferenceDensity
    (isProbabilityDensity_uniformSimplex m ha) (isProbabilityDensity_uniformSimplex m hb)
  have hv : 0 < (volume (simplex m 1)).toReal :=
    ENNReal.toReal_pos (volume_unit_simplex_pos m).ne' (volume_simplex_ne_top m 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have he (z : Fin m → ℝ) : overlapRadius a b z ^ m = D * d z := by
    dsimp [D, d]
    rw [crossDifferenceDensity_uniformSimplex m ha hb]
    field_simp
  calc
    (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (overlapRadius a b z ^ m)) =
        ∫⁻ z, ENNReal.ofReal D * ENNReal.ofReal (d z) := by
      apply lintegral_congr
      intro z
      rw [he, ENNReal.ofReal_mul hD.le]
    _ = ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (d z) :=
      lintegral_const_mul _ hd.1.ennreal_ofReal
    _ = ENNReal.ofReal D := by
      rw [← ofReal_integral_eq_lintegral_ofReal hd.2.2.1
        (Filter.Eventually.of_forall hd.2.1), hd.2.2.2, ENNReal.ofReal_one, mul_one]

/-- Normalization as an actual real polynomial integral, before binomial expansion. -/
theorem orthant_polynomial_moment_normalization (m : ℕ) [NeZero m] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (∫ t in 0..b, orthantVolumePolynomial m a b t * ((m : ℝ) * t ^ (m - 1))) =
      a ^ m * b ^ m * (volume (simplex m 1)).toReal := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let f : ℝ → ℝ := fun t => orthantVolumePolynomial m a b t * ((m : ℝ) * t ^ (m - 1))
  have hcont : Continuous f := (continuous_orthantVolumePolynomial m a b).mul
    (continuous_const.mul (continuous_id.pow _))
  have hfint : IntegrableOn f (Ioo 0 b) volume :=
    (hcont.intervalIntegrable 0 b).1.mono_set Ioo_subset_Ioc_self
  have hfnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ f t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact mul_nonneg (orthantVolumePolynomial_nonneg m (ht.2.le.trans hba) ht.2.le)
      (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg ht.1.le _))
  have hmoment := lintegral_overlapRadius_pow_orthants m m hm hb.le hba
  rw [lintegral_overlapRadius_pow_normalization m ha hb] at hmoment
  have he : (∫⁻ t in Ioo (0 : ℝ) b,
      ENNReal.ofReal (orthantVolumePolynomial m a b t) *
        ENNReal.ofReal ((m : ℝ) * t ^ (m - 1))) = ENNReal.ofReal (∫ t in 0..b, f t) := by
    rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hfint hfnn]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact (ENNReal.ofReal_mul (orthantVolumePolynomial_nonneg m
      (ht.2.le.trans hba) ht.2.le)).symm
  have hcurve : ENNReal.ofReal (a ^ m * b ^ m * (volume (simplex m 1)).toReal) =
      ∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal (orthantVolumePolynomial m a b t) *
          ENNReal.ofReal ((m : ℝ) * t ^ (m - 1)) := by
    rw [hmoment]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [← volume_overlap_superlevel m ht.1 (ht.2.trans_le hba) ht.2,
      volume_overlap_superlevel_eq_ofReal_polynomial m ht.1 (ht.2.trans_le hba) ht.2]
  rw [he] at hcurve
  have hleft : 0 ≤ ∫ t in 0..b, f t := by
    rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    exact integral_nonneg_of_ae hfnn
  have hright : 0 ≤ a ^ m * b ^ m * (volume (simplex m 1)).toReal := by positivity
  have hc := congrArg ENNReal.toReal hcurve
  simpa only [ENNReal.toReal_ofReal hright, ENNReal.toReal_ofReal hleft] using hc.symm

end EntropicRogersShephard
