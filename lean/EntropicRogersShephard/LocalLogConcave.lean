import EntropicRogersShephard.CompactExponentialBound
import EntropicRogersShephard.LogConcavity

/-! The sharp bound for normalized restrictions to compact convex subsets of the positive interior. -/

open MeasureTheory Set Real
open scoped ENNReal

namespace EntropicRogersShephard

noncomputable def logPotential {n : ℕ} (C : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => Real.log C - Real.log (f x)

theorem measurable_logPotential {n : ℕ} (C : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (logPotential C f) := measurable_const.sub hf.log

theorem convexOn_logPotential {n : ℕ} (C : ℝ) {K : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : IsLogConcave n f) (hK : Convex ℝ K)
    (hs : K ⊆ {x | 0 < f x}) : ConvexOn ℝ K (logPotential C f) :=
  (convexOn_const (Real.log C) hK).sub ((concaveOn_log_of_isLogConcave hf).subset hs hK)

theorem logPotential_bounds {n : ℕ} {K : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {c C : ℝ} (hc : 0 < c) (hb : ∀ x ∈ K, f x ∈ Icc c C) {x : Fin n → ℝ} (hx : x ∈ K) :
    logPotential C f x ∈ Icc (0 : ℝ) (Real.log C - Real.log c) :=
  ⟨sub_nonneg.mpr (Real.log_le_log (hc.trans_le (hb x hx).1) (hb x hx).2),
    sub_le_sub_left (Real.log_le_log hc (hb x hx).1) _⟩

theorem exponential_logPotential_eq {n : ℕ} {K : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {C : ℝ} (hC : 0 < C) (hp : ∀ x ∈ K, 0 < f x) :
    EqOn (fun x => Real.exp (-logPotential C f x)) (fun x => C⁻¹ * f x) K := by
  intro x hx
  simp only [logPotential, neg_sub, Real.exp_sub, Real.exp_log (hp x hx), Real.exp_log hC,
    div_eq_mul_inv, mul_comm]

theorem compact_restriction_entropy_finite_and_bound {n : ℕ} {K : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hK : IsCompact K) (hconv : Convex ℝ K) (hpos : volume K ≠ 0)
    (hm : Measurable f) (hl : IsLogConcave n f) (hs : K ⊆ interior {x | 0 < f x}) :
    Integrable (fun x => Real.negMulLog (powerDensity 1 K f x)) volume ∧
      Integrable (fun s => Real.negMulLog (differenceDensity (powerDensity 1 K f) s)) volume ∧
      differentialEntropy (differenceDensity (powerDensity 1 K f)) volume -
        differentialEntropy (powerDensity 1 K f) volume ≤ (n : ℝ) * Real.log 2 := by
  have hne : K.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hpos
  obtain ⟨c, C, hc, hC, hb⟩ := compact_positiveInterior_bounds hl hK hne hs
  let V := logPotential C f
  have hVmeas : Measurable V := measurable_logPotential C hm
  have hVcont : ContinuousOn V K :=
    continuousOn_const.sub ((continuousOn_log_positiveInterior hl).mono hs)
  have hVconv : ConvexOn ℝ K V := convexOn_logPotential C hl hconv (hs.trans interior_subset)
  have hVb : ∀ x ∈ K, V x ∈ Icc (0 : ℝ) (Real.log C - Real.log c) := fun _ hx => logPotential_bounds hc hb hx
  obtain ⟨x, hx⟩ := hne
  have hR : 0 ≤ Real.log C - Real.log c := (hVb x hx).1.trans (hVb x hx).2
  have h := compact_exponential_entropy_finite_and_bound hK hpos hVmeas hVcont hVconv hR hVb
  have hEq : EqOn (fun x => Real.exp (-V x)) (fun x => C⁻¹ * f x) K :=
    exponential_logPotential_eq hC (fun x hx => hc.trans_le (hb x hx).1)
  have hd : compactExponentialDensity K V = powerDensity 1 K f := by
    change powerDensity 1 K (fun x => Real.exp (-V x)) = powerDensity 1 K f
    rw [powerDensity_congr_on_support hEq, powerDensity_one_const_mul f (inv_ne_zero hC.ne')]
  rw [hd] at h
  exact h

end EntropicRogersShephard
