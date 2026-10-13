/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeDerivativeFlux
import RicciFlowSharpEstimate.Analysis.DivergenceMaximumPrinciple

/-!
# Maximum principle in the actual recoverable weak probe domain

The actual weighted graph supplies the absolutely continuous derivative flux
and its zero pole traces. A nonpositive weak meridional operator therefore
forces the continuous probe to be nonnegative in the physical interior. No
classical second derivative, probe endpoint value, or admissible absolute-value
replacement is assumed. The source sign itself remains an explicit hypothesis.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A nonpositive actual weak meridional operator forces a continuous recoverable
probe to be nonnegative in the physical interior. The weighted graph proves the
required zero flux traces; no probe boundary values or global C² regularity enter. -/
theorem IsRecoverableAreaCompetitor.nonneg_of_weakMeridionalOperator_nonpos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hq : ∀ᵐ x ∂areaμ, weakMeridionalOperator K r p z x ≤ 0) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ r x := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  obtain ⟨hGAC, hG0, hG1, hGD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  have hGC : ContinuousOn (weakProbeDerivativeFlux K p) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hGAC.continuousOn
  apply Analysis.nonneg_of_divergence_inequality zero_lt_one r
    (fun x => warp K x ^ 2) (weakProbeDerivativeFlux K p)
    (fun x => warp K x * (weakMeridionalOperator K r p z x + K x * r x))
    (fun x => warp K x * K x)
    (h.2.1.weakDeriv.contDiffOn_one_of_continuousOn hr hp) hGC hG0 hG1
    ?_ ?_ (fun x _ => sq_nonneg (warp K x)) hGD ?_ ?_
  · intro a ha b hb hab
    apply hGAC.mono
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    intro x hx
    exact ⟨ha.1.le.trans hx.1, hx.2.trans hb.2.le⟩
  · intro x hx
    simp only [weakProbeDerivativeFlux,
      (h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hx).deriv]
  · filter_upwards [hq, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hprod := mul_nonpos_of_nonneg_of_nonpos (hfpos x hxI).le hx
    nlinarith only [hprod]
  · filter_upwards [hg.2.2.2.2, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact mul_pos (hfpos x hxI) ((by positivity : (0 : ℝ) < 2 / C).trans_le hx.1)

end RicciFlowSharpEstimate.Geometry.AreaProfile
