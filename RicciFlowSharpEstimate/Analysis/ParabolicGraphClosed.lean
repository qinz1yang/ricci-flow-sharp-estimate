/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import RicciFlowSharpEstimate.Analysis.WeightedWeakDerivativeLimit
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers

/-!
# Closedness of the parabolic weak derivative graph

Strong convergence in the three weighted coordinates preserves both genuine
weak derivatives of the displayed limit functions. Membership of the limiting
coordinates is derived from the limits; no independently supplied derivative
or locally integrable representative is required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem memLp_of_strong_two_limit
    {F : ℕ → ℝ → ℝ} {F0 : ℝ → ℝ}
    (hF : ∀ n, MemLp (F n) 2 areaμ)
    (hlim : Tendsto (fun n ↦ eLpNorm (F n - F0) 2 areaμ) atTop (𝓝 0)) :
    MemLp F0 2 areaμ := by
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by simp))).exists
  have hd : MemLp (F n - F0) 2 areaμ := hn.trans (by simp)
  convert (hF n).sub hd using 1
  funext x
  simp only [Pi.sub_apply, sub_sub_cancel]

private theorem closed_graph_weighted_test_pairing_tendsto
    {a F0 : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (ha : Continuous a) (ha0 : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0)
    (hF : ∀ n, MemLp (fun x ↦ a x * F n x) 2 areaμ)
    (hF0 : MemLp F0 2 areaμ)
    (hlim : Tendsto (fun n ↦ eLpNorm ((fun x ↦ a x * F n x) - F0) 2 areaμ)
      atTop (𝓝 0))
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφI : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ ∫ x, φ x * F n x) atTop
      (𝓝 (∫ x, φ x * (F0 x / a x))) := by
  have ht := memLp_two_Ioo_div_test ha ha0 hφ hφc hφI
  have hz : Tendsto (fun _ : ℕ ↦ eLpNorm
      ((fun x ↦ φ x / a x) - (fun x ↦ φ x / a x)) 2 areaμ) atTop (𝓝 0) := by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have hp := (tendsto_integral_mul_of_tendsto_eLpNorm_two
    hF hF0 (fun _ ↦ ht) ht hlim hz).2.2
  have hφzero (x : ℝ) (hx : x ∉ Ioo (0 : ℝ) 1) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hxt ↦ hx (hφI hxt)
  have hsource (n : ℕ) :
      (∫ x, (a x * F n x) * (φ x / a x) ∂areaμ) = ∫ x, φ x * F n x := by
    calc
      _ = ∫ x in Ioo (0 : ℝ) 1, φ x * F n x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        field_simp [ha0 x hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        simp only [hφzero x hx, zero_mul]
  have htarget : (∫ x, F0 x * (φ x / a x) ∂areaμ) =
      ∫ x, φ x * (F0 x / a x) := by
    calc
      _ = ∫ x in Ioo (0 : ℝ) 1, φ x * (F0 x / a x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        simp only [hφzero x hx, zero_mul]
  simpa only [hsource, htarget] using hp

private theorem closed_graph_weak_derivative_of_weighted_limits
    {a b R0 P0 : ℝ → ℝ} {R P : ℕ → ℝ → ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0)
    (hb0 : ∀ x ∈ Ioo (0 : ℝ) 1, b x ≠ 0)
    (hseq : ∀ n, HasWeakDerivOn (Ioo (0 : ℝ) 1) (R n) (P n))
    (hR : ∀ n, MemLp (fun x ↦ a x * R n x) 2 areaμ)
    (hP : ∀ n, MemLp (fun x ↦ b x * P n x) 2 areaμ)
    (hR0 : MemLp R0 2 areaμ) (hP0 : MemLp P0 2 areaμ)
    (hRL : Tendsto (fun n ↦ eLpNorm ((fun x ↦ a x * R n x) - R0) 2 areaμ)
      atTop (𝓝 0))
    (hPL : Tendsto (fun n ↦ eLpNorm ((fun x ↦ b x * P n x) - P0) 2 areaμ)
      atTop (𝓝 0)) :
    HasWeakDerivOn (Ioo (0 : ℝ) 1) (fun x ↦ R0 x / a x) (fun x ↦ P0 x / b x) := by
  apply HasWeakDerivOn.of_tendsto_test_pairings hseq
    (locallyIntegrableOn_Ioo_div_weight ha ha0 hR0)
    (locallyIntegrableOn_Ioo_div_weight hb hb0 hP0)
  · intro φ hφ hφc hφI
    exact closed_graph_weighted_test_pairing_tendsto ha ha0 hR hR0 hRL (deriv φ)
      (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφI)
  · intro φ hφ hφc hφI
    exact closed_graph_weighted_test_pairing_tendsto hb hb0 hP hP0 hPL φ hφ.continuous hφc hφI

/-- A strong limit in the three canonical parabolic graph coordinates retains
both genuine weak derivative identities for those exact displayed functions.
The three weighted membership conditions are consequences of the limits. -/
theorem hasParabolicWeakDerivatives_of_strong_graph
    {rs ps zs : ℕ → ℝ → ℝ} {r p z : ℝ → ℝ}
    (h : ∀ n, HasParabolicWeakDerivatives (rs n) (ps n) (zs n))
    (hR : Tendsto (fun n ↦ eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0))
    (hP : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * ps n x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0))
    (hZ : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * zs n x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
      atTop (𝓝 0)) :
    HasParabolicWeakDerivatives r p z := by
  let a : ℝ → ℝ := fun x ↦ Real.sqrt (x * (1 - x))
  let b : ℝ → ℝ := fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x))
  have ha : Continuous a := by dsimp only [a]; fun_prop
  have hb : Continuous b := by dsimp only [b]; fun_prop
  have ha0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : a x ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hx.1 (sub_pos.mpr hx.2))).ne'
  have hb0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : b x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx.1.ne' (sub_pos.mpr hx.2).ne') (ha0 x hx)
  have hrmem := memLp_of_strong_two_limit (fun n ↦ (h n).memLp) hR
  have hpmem := memLp_of_strong_two_limit (fun n ↦ (h n).memLp_weighted_deriv) hP
  have hzmem := memLp_of_strong_two_limit (fun n ↦ (h n).memLp_weighted_secondDeriv) hZ
  have hpeq : (fun x ↦ (a x * p x) / a x) =ᵐ[areaμ] p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    field_simp [ha0 x hx]
  have hzeq : (fun x ↦ (b x * z x) / b x) =ᵐ[areaμ] z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    field_simp [hb0 x hx]
  have hfirst : HasWeakDerivOn (Ioo (0 : ℝ) 1) r (fun x ↦ (a x * p x) / a x) := by
    have hRmem : ∀ n, MemLp (fun x ↦ (1 : ℝ) * rs n x) 2 areaμ := by
      simpa only [one_mul] using fun n ↦ (h n).memLp
    have hRL : Tendsto (fun n ↦ eLpNorm ((fun x ↦ (1 : ℝ) * rs n x) - r) 2 areaμ)
        atTop (𝓝 0) := by simpa only [one_mul] using hR
    simpa only [div_one] using closed_graph_weak_derivative_of_weighted_limits
      continuous_const ha (fun _ _ ↦ one_ne_zero) ha0
      (fun n ↦ (h n).weakDeriv) hRmem (fun n ↦ (h n).memLp_weighted_deriv)
      hrmem hpmem hRL hP
  have hsecond := closed_graph_weak_derivative_of_weighted_limits ha hb ha0 hb0
    (fun n ↦ (h n).weakDeriv_deriv) (fun n ↦ (h n).memLp_weighted_deriv)
    (fun n ↦ (h n).memLp_weighted_secondDeriv) hpmem hzmem hP hZ
  exact ⟨hfirst.congr_ae ae_eq_rfl hpeq, hsecond.congr_ae hpeq hzeq,
    hrmem, hpmem, hzmem⟩

end RicciFlowSharpEstimate.Analysis
