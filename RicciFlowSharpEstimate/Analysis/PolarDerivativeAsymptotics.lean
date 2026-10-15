/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic endpoint asymptotics from an almost-everywhere derivative limit

An absolutely continuous function anchored at zero has a quadratic leading
term when its derivative divided by the coordinate has an essential right
limit. The conclusion is an ordinary right limit of the actual function.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set Topology

/-- An essential right limit of the genuine derivative divided by the
coordinate determines the ordinary right limit of the quadratic quotient
of an absolutely continuous function vanishing at zero. -/
theorem tendsto_div_sq_of_ae_derivative_quotient
    {F : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hF : AbsolutelyContinuousOnInterval F 0 b) (hF0 : F 0 = 0)
    (hlim : Tendsto (fun x => deriv F x / x)
      ((𝓝[>] (0 : ℝ)) ⊓ ae volume) (𝓝 L)) :
    Tendsto (fun x => F x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun x => |deriv F x / x - L|)
      ((𝓝[>] (0 : ℝ)) ⊓ ae volume) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hlim.sub_const L).abs
  have hnear : ∀ᶠ x in (𝓝[>] (0 : ℝ)) ⊓ ae volume,
      |deriv F x / x - L| < ε := herror.eventually (gt_mem_nhds hε)
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_inf.mp hnear
  obtain ⟨d, hd, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hU
  have hδ : 0 < min b d := lt_min hb hd
  filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
  have hxb : x < b := hx.2.trans_le (min_le_left b d)
  have hxd : x < d := hx.2.trans_le (min_le_right b d)
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hx.1.le, uIcc_of_le hb.le]
    exact Icc_subset_Icc le_rfl hxb.le
  have hFx : (∫ t in 0..x, deriv F t) = F x := by
    simpa only [hF0, sub_zero] using (hF.mono hsub).integral_deriv_eq_sub
  have hlinear (C : ℝ) : (∫ t in 0..x, C * t) = C * x ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hInt : (∫ t in 0..x, deriv F t - L * t) = F x - L * x ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (hF.mono hsub).intervalIntegrable_deriv
      (show IntervalIntegrable (fun t : ℝ => L * t) volume 0 x from
        ((continuous_const.mul continuous_id).intervalIntegrable 0 x)), hFx, hlinear L]
  have hdom : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) x →
      ‖deriv F t - L * t‖ ≤ ε * t := by
    filter_upwards [hV] with t htV htI
    have hq : |deriv F t / t - L| ≤ ε :=
      (hUV t ⟨hlocal ⟨htI.1, htI.2.trans_lt hxd⟩, htV⟩).le
    have hid : deriv F t - L * t = (deriv F t / t - L) * t := by
      field_simp [htI.1.ne']
    rw [Real.norm_eq_abs, hid, abs_mul, abs_of_pos htI.1]
    exact mul_le_mul_of_nonneg_right hq htI.1.le
  have hquad : |F x - L * x ^ 2 / 2| ≤ ε * x ^ 2 / 2 := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hx.1.le hdom
      ((continuous_const.mul continuous_id).intervalIntegrable 0 x)
    simpa only [Real.norm_eq_abs, hInt, hlinear ε] using hnorm
  have hquot : F x / x ^ 2 - L / 2 = (F x - L * x ^ 2 / 2) / x ^ 2 := by
    field_simp [hx.1.ne']
  rw [Real.dist_eq, hquot, abs_div, abs_of_pos (sq_pos_of_pos hx.1)]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply (div_le_iff₀ (sq_pos_of_pos hx.1)).mpr
  calc
    |F x - L * x ^ 2 / 2| ≤ ε * x ^ 2 / 2 := hquad
    _ = ε / 2 * x ^ 2 := by ring

end RicciFlowSharpEstimate.Analysis
