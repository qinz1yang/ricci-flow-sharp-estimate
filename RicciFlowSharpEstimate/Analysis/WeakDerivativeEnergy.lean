/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev

/-!
# Interior energy estimates at a double zero

The continuous representatives of a genuine second weak derivative graph have
quantitative decay at a common zero. All energies are taken on compact interior
intervals; no pole trace, pointwise second derivative or differentiability of a
coefficient is used.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory

/-- The square of an increment of a continuous weakly differentiable function
is bounded by interval length times the square integral of its genuine weak
derivative. -/
theorem HasWeakDerivOn.sq_sub_le_length_mul_integral_sq
    {a b u v : ℝ} {r p : ℝ → ℝ}
    (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b))
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v)
    (hp2 : IntervalIntegrable (fun t ↦ p t ^ 2) volume u v) :
    (r v - r u) ^ 2 ≤ (v - u) * (∫ t in u..v, p t ^ 2) := by
  by_cases heq : u = v
  · subst v
    simp
  have hpos : 0 < v - u := sub_pos.mpr (lt_of_le_of_ne huv heq)
  have hsub : Icc u v ⊆ Ioo a b := by
    intro x hx
    exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
  have hpI : IntervalIntegrable p volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
      (h.locallyIntegrable_deriv.integrableOn_compact_subset hsub isCompact_Icc)
  have hFTC := h.integral_eq_sub_of_continuousOn hr hu hv
  have hA : IntervalIntegrable (fun t ↦ (v - u) ^ 2 * p t ^ 2) volume u v :=
    hp2.const_mul _
  have hB : IntervalIntegrable
      (fun t ↦ (2 * (v - u) * (r v - r u)) * p t) volume u v :=
    hpI.const_mul _
  have hidentity :
      (∫ t in u..v, ((v - u) * p t - (r v - r u)) ^ 2) =
        (v - u) * ((v - u) * (∫ t in u..v, p t ^ 2) - (r v - r u) ^ 2) := by
    calc
      _ = ∫ t in u..v,
          ((v - u) ^ 2 * p t ^ 2 -
            (2 * (v - u) * (r v - r u)) * p t) + (r v - r u) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hA.sub hB) intervalIntegrable_const,
          intervalIntegral.integral_sub hA hB,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, hFTC]
        simp only [smul_eq_mul]
        ring
  have hnonneg : 0 ≤ ∫ t in u..v,
      ((v - u) * p t - (r v - r u)) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall huv (fun t ↦ sq_nonneg _)
  rw [hidentity] at hnonneg
  have hmul :
      (v - u) * (r v - r u) ^ 2 ≤
        (v - u) * ((v - u) * (∫ t in u..v, p t ^ 2)) := by
    nlinarith only [hnonneg]
  exact le_of_mul_le_mul_left hmul hpos

/-- At a double zero, both the continuous probe and its continuous genuine
first derivative have the decay required by a shrinking second-order cutoff.
The energy is the unweighted second-derivative energy on the indicated compact
interior interval, with no regularity assumed of the second derivative. -/
theorem HasParabolicWeakDerivatives.sq_le_energy_of_double_zero_left
    {r p z : ℝ → ℝ} {a c x : ℝ}
    (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Icc a c) (hrc : r c = 0) (hpc : p c = 0) :
    p x ^ 2 ≤ (c - x) * (∫ t in a..c, z t ^ 2) ∧
    r x ^ 2 ≤ (c - x) ^ 3 * (∫ t in a..c, z t ^ 2) := by
  have hac : a ≤ c := hx.1.trans hx.2
  have hsub : Icc a c ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨ha.1.trans_le hy.1, hy.2.trans_lt hc.2⟩
  have hz2 : IntervalIntegrable (fun t ↦ z t ^ 2) volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hac).mpr
      (h.memLp_secondDeriv_compact isCompact_Icc hsub).integrable_sq
  have hE : 0 ≤ ∫ t in a..c, z t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hac (fun t ↦ sq_nonneg _)
  have hpbound (y : ℝ) (hy : y ∈ Icc a c) :
      p y ^ 2 ≤ (c - y) * (∫ t in a..c, z t ^ 2) := by
    have hyc : Icc y c ⊆ Icc a c := by
      intro t ht
      exact ⟨hy.1.trans ht.1, ht.2⟩
    have hz2yc : IntervalIntegrable (fun t ↦ z t ^ 2) volume y c :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hy.2).mpr
        ((h.memLp_secondDeriv_compact isCompact_Icc (hyc.trans hsub)).integrable_sq)
    have hinc := h.weakDeriv_deriv.sq_sub_le_length_mul_integral_sq
      hp (hsub hy) hc hy.2 hz2yc
    have hmono : (∫ t in y..c, z t ^ 2) ≤ ∫ t in a..c, z t ^ 2 :=
      intervalIntegral.integral_mono_interval hy.1 hy.2 le_rfl
        (Filter.Eventually.of_forall fun t ↦ sq_nonneg _) hz2
    have hscaled := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hy.2)
    have hinc' : p y ^ 2 ≤ (c - y) * (∫ t in y..c, z t ^ 2) := by
      simpa only [hpc, zero_sub, neg_sq] using hinc
    exact hinc'.trans hscaled
  have hxcsub : Icc x c ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact hsub ⟨hx.1.trans hy.1, hy.2⟩
  have hp2 : IntervalIntegrable (fun t ↦ p t ^ 2) volume x c :=
    (hp.mono hxcsub).pow 2 |>.intervalIntegrable_of_Icc hx.2
  have hrinc := h.weakDeriv.sq_sub_le_length_mul_integral_sq
    hr (hsub hx) hc hx.2 hp2
  have hpint : (∫ t in x..c, p t ^ 2) ≤
      (c - x) ^ 2 * (∫ t in a..c, z t ^ 2) := by
    calc
      _ ≤ ∫ _t in x..c, (c - x) * (∫ s in a..c, z s ^ 2) := by
        apply intervalIntegral.integral_mono_on hx.2 hp2 intervalIntegrable_const
        intro y hy
        exact (hpbound y ⟨hx.1.trans hy.1, hy.2⟩).trans
          (mul_le_mul_of_nonneg_right (sub_le_sub_left hy.1 c) hE)
      _ = _ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  refine ⟨hpbound x hx, ?_⟩
  have hrinc' : r x ^ 2 ≤ (c - x) * (∫ t in x..c, p t ^ 2) := by
    simpa only [hrc, zero_sub, neg_sq] using hrinc
  calc
    _ ≤ (c - x) * (∫ t in x..c, p t ^ 2) := hrinc'
    _ ≤ (c - x) * ((c - x) ^ 2 * (∫ t in a..c, z t ^ 2)) :=
      mul_le_mul_of_nonneg_left hpint (sub_nonneg.mpr hx.2)
    _ = _ := by ring

end RicciFlowSharpEstimate.Analysis
