import EntropicRogersShephard.ProbabilityLaw
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Finite product densities and their entropy, with the zero factors included. -/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def productDensity (n : ℕ) (f : ℝ → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∏ i, f (x i)

def ScalarLogConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    Real.rpow (f x) a * Real.rpow (f y) b ≤ f (a * x + b * y)

theorem measurable_productDensity (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (productDensity n f) := by
  unfold productDensity
  fun_prop

theorem productDensity_nonneg (n : ℕ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Fin n → ℝ) :
    0 ≤ productDensity n f x := Finset.prod_nonneg (fun i _ => hf (x i))

theorem integrable_productDensity (n : ℕ) {f : ℝ → ℝ} (hf : Integrable f volume) :
    Integrable (productDensity n f) volume := Integrable.fintype_prod (fun _ => hf)

theorem integral_productDensity (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, productDensity n f x) = (∫ t, f t) ^ n := by
  simpa only [productDensity, Fintype.card_fin] using
    integral_fintype_prod_volume_eq_pow (ι := Fin n) f

theorem isProbabilityDensity_productDensity (n : ℕ) {f : ℝ → ℝ}
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (hi : Integrable f volume) (h1 : (∫ t, f t) = 1) :
    IsProbabilityDensity n (productDensity n f) := by
  refine ⟨measurable_productDensity n hm, productDensity_nonneg n hn,
    integrable_productDensity n hi, ?_⟩
  rw [integral_productDensity, h1, one_pow]

theorem isLogConcave_productDensity (n : ℕ) {f : ℝ → ℝ}
    (hn : ∀ x, 0 ≤ f x) (hl : ScalarLogConcave f) : IsLogConcave n (productDensity n f) := by
  intro x y a b ha hb hab
  unfold productDensity
  simp only [Real.rpow_eq_pow]
  rw [← Real.finsetProd_rpow univ (fun i => f (x i)) (fun i _ => hn (x i)) a,
    ← Real.finsetProd_rpow univ (fun i => f (y i)) (fun i _ => hn (y i)) b,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    exact mul_nonneg (Real.rpow_nonneg (hn _) _) (Real.rpow_nonneg (hn _) _)
  · intro i _
    change Real.rpow (f (x i)) a * Real.rpow (f (y i)) b ≤ f (a * x i + b * y i)
    exact hl (x i) (y i) a b ha hb hab

theorem productDensity_coordinate_moment {n : ℕ} {f k : ℝ → ℝ}
    (hf : Integrable f volume) (h1 : (∫ t, f t) = 1)
    (hk : Integrable (fun t => f t * k t) volume) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => productDensity n f x * k (x i)) volume ∧
      (∫ x : Fin n → ℝ, productDensity n f x * k (x i)) = ∫ t, f t * k t := by
  classical
  let u (j : Fin n) (t : ℝ) := (if j = i then k t else 1) * f t
  have hui (j : Fin n) : Integrable (u j) volume := by
    by_cases hj : j = i
    · subst j
      simpa [u, mul_comm] using hk
    · simpa only [u, if_neg hj, one_mul] using hf
  have he (x : Fin n → ℝ) : (∏ j, u j (x j)) = productDensity n f x * k (x i) := by
    simp only [u, productDensity]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hef : (fun x : Fin n → ℝ => ∏ j, u j (x j)) =
      (fun x => productDensity n f x * k (x i)) := funext he
  have hi : Integrable (fun x : Fin n → ℝ => productDensity n f x * k (x i)) volume := by
    rw [← hef]
    exact Integrable.fintype_prod hui
  refine ⟨hi, ?_⟩
  rw [← hef, integral_fintype_prod_volume_eq_prod]
  have hqi (j : Fin n) : (∫ t, u j t) = if j = i then (∫ t, f t * k t) else 1 := by
    by_cases hj : j = i
    · subst j
      simp [u, mul_comm]
    · simp only [u, if_neg hj, one_mul, h1]
  simp_rw [hqi]
  simp

theorem productDensity_sum_moment (n : ℕ) {f k : ℝ → ℝ}
    (hf : Integrable f volume) (h1 : (∫ t, f t) = 1)
    (hk : Integrable (fun t => f t * k t) volume) :
    Integrable (fun x : Fin n → ℝ => productDensity n f x * ∑ i, k (x i)) volume ∧
      (∫ x : Fin n → ℝ, productDensity n f x * ∑ i, k (x i)) =
        (n : ℝ) * ∫ t, f t * k t := by
  have hi (i : Fin n) := (productDensity_coordinate_moment hf h1 hk i).1
  have he : (fun x : Fin n → ℝ => productDensity n f x * ∑ i, k (x i)) =
      (fun x => ∑ i, productDensity n f x * k (x i)) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [(productDensity_coordinate_moment hf h1 hk _).2]
  simp

theorem negMulLog_productDensity (n : ℕ) (f : ℝ → ℝ) (x : Fin n → ℝ) :
    Real.negMulLog (productDensity n f x) = productDensity n f x * ∑ i, -Real.log (f (x i)) := by
  classical
  by_cases hp : productDensity n f x = 0
  · simp [hp]
  · have hn : ∀ i ∈ (Finset.univ : Finset (Fin n)), f (x i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hp
    simp only [productDensity, Real.negMulLog_def, Real.log_prod hn, Finset.sum_neg_distrib]
    ring

theorem productDensity_entropy (n : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f volume) (h1 : (∫ t, f t) = 1)
    (hh : Integrable (fun t => Real.negMulLog (f t)) volume) :
    Integrable (fun x => Real.negMulLog (productDensity n f x)) volume ∧
      differentialEntropy (productDensity n f) volume = (n : ℝ) * differentialEntropy f volume := by
  have he : (fun t => f t * -Real.log (f t)) = (fun t => Real.negMulLog (f t)) := by
    funext t
    simp only [Real.negMulLog_def]
    ring
  have hk : Integrable (fun t => f t * -Real.log (f t)) volume := by rw [he]; exact hh
  have h := productDensity_sum_moment n hf h1 hk
  have hg : (fun x => Real.negMulLog (productDensity n f x)) =
      (fun x => productDensity n f x * ∑ i, -Real.log (f (x i))) :=
    funext (negMulLog_productDensity n f)
  rw [← hg, he] at h
  exact h

end EntropicRogersShephard
