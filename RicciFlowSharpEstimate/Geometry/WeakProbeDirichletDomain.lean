/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicBoundary
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity

/-!
# The natural Dirichlet domain of the transformed weak probe

Multiplying the actual probe by its actual warp gives an absolutely continuous
function with zero endpoint traces and square-integrable derivative. The local
second-order equation follows from the tied weak jets and curvature primitives.
Only the transformed function has zero boundary values; the probe does not.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The literal product of a recoverable probe and its warp is a zero-trace
H¹ representative, with its actual square-integrable product derivative. -/
theorem IsRecoverableAreaCompetitor.transformed_probe_absolutelyContinuous
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) :
    AbsolutelyContinuousOnInterval (fun x => warp K x * r x) 0 1 ∧
      warp K 0 * r 0 = 0 ∧ warp K 1 * r 1 = 0 ∧
      MemLp (fun x => warp K x * r x) 2 areaμ ∧
      MemLp (fun x => warpSlope K x * r x + warp K x * p x) 2 areaμ ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (fun y => warp K y * r y)
        (warpSlope K x * r x + warp K x * p x) x) := by
  have hg := h.geometry_bounds hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  apply h.2.1.weakDeriv.absolutelyContinuous_mul_of_parabolic_bounds
    (h.primitive_weak_derivatives hC).1 hr (hg.1.mono Ioo_subset_Icc_self)
    h.2.1.memLp h.2.1.memLp_weighted_deriv (B := 2 * C)
  · intro x hx
    have hb := hg.2.2.1 x hx
    have h0 : 0 ≤ warp K x := by
      apply le_trans ?_ hb.1
      exact mul_nonneg (mul_nonneg (by positivity) hx.1) (sub_nonneg.mpr hx.2)
    simpa only [abs_of_nonneg h0, mul_assoc] using hb.2.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2).trans (by linarith)

/-- The actual transformed derivative is locally absolutely continuous and
solves y'' + (K/f)y = q almost everywhere. All fields are the same original
curvature and weak jets; division occurs only in the positive-warp interior. -/
theorem IsRecoverableAreaCompetitor.transformed_probe_equation
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1)) :
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval
        (fun x => warpSlope K x * r x + warp K x * p x) a b) ∧
      (∀ᵐ x ∂areaμ,
        HasDerivAt (fun y => warpSlope K y * r y + warp K y * p y)
          (weakMeridionalOperator K r p z x -
            (K x / warp K x) * (warp K x * r x)) x) := by
  have hg := h.geometry_bounds hC
  have hw := h.primitive_weak_derivatives hC
  have hloc := h.primitive_local_regularity hC
  constructor
  · intro a ha b hb
    have hba := hw.2.absolutelyContinuousOnInterval
      (hg.2.1.mono Ioo_subset_Icc_self) ha hb
    have hfa := hw.1.absolutelyContinuousOnInterval
      (hg.1.mono Ioo_subset_Icc_self) ha hb
    have hra := h.2.1.weakDeriv.absolutelyContinuousOnInterval hr ha hb
    have hpa := h.2.1.weakDeriv_deriv.absolutelyContinuousOnInterval hp ha hb
    exact (hba.mul hra).fun_add (hfa.mul hpa)
  · filter_upwards [hloc.2.2,
      h.2.1.weakDeriv.ae_hasDerivAt_of_continuousOn hr,
      h.2.1.weakDeriv_deriv.ae_hasDerivAt_of_continuousOn hp,
      ae_restrict_mem measurableSet_Ioo] with x hbx hrx hpx hx
    have hd := (hbx.mul hrx).add ((hloc.1 x hx).mul hpx)
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hfpos : 0 < warp K x :=
      (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
        (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
    convert hd using 1
    dsimp only [weakMeridionalOperator]
    field_simp [hfpos.ne']
    ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
