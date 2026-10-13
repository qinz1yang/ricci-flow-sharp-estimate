/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeMaximumPrinciple
import RicciFlowSharpEstimate.Analysis.DivergenceStrongMaximum

/-!
# Strict positivity in the actual weak probe domain

The zero-flux maximum principle first supplies nonnegativity. Local strict
ellipticity of the physical warp and a bounded curvature coefficient then
exclude an interior zero for the same unit-mass competitor. The actual weak
operator need only be nonpositive almost everywhere. Its sign remains an
explicit assumption, and no raw endpoint value is constrained.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A nonpositive actual weak meridional operator forces strict positivity of a
continuous recoverable unit-mass probe throughout the physical interior. The
nonzero point follows from its actual mass, not an extra sign or source premise. -/
theorem IsRecoverableAreaCompetitor.pos_of_weakMeridionalOperator_nonpos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hq : ∀ᵐ x ∂areaμ, weakMeridionalOperator K r p z x ≤ 0) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 < r x := by
  have hnonneg := h.nonneg_of_weakMeridionalOperator_nonpos hC hr hp hq
  have hpos : ∃ x ∈ Ioo (0 : ℝ) 1, 0 < r x := by
    by_contra hn
    push Not at hn
    have hz (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : r x = 0 :=
      le_antisymm (hn x hx) (hnonneg x hx)
    have hm : probeMass K r = 0 := by
      unfold probeMass
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [hz x hx, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Pi.zero_apply]
    have hmass : probeMass K r = 1 := h.2.2.2.2.2.1
    linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hf := hg.1.mono Ioo_subset_Icc_self
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  obtain ⟨hGAC, _, _, hGD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  apply Analysis.pos_of_divergence_inequality_of_nonneg r
    (fun x => warp K x ^ 2) (weakProbeDerivativeFlux K p)
    (fun x => warp K x * (weakMeridionalOperator K r p z x + K x * r x))
    (fun x => (2 * C) * warp K x)
    (h.2.1.weakDeriv.contDiffOn_one_of_continuousOn hr hp)
    ?_ ?_ (hf.pow 2) (fun x hx => sq_pos_of_pos (hfpos x hx))
    (continuousOn_const.mul hf) hGD ?_ hnonneg hpos
  · intro a ha b hb hab
    apply hGAC.mono
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    intro x hx
    exact ⟨ha.1.le.trans hx.1, hx.2.trans hb.2.le⟩
  · intro x hx
    simp only [weakProbeDerivativeFlux,
      (h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hx).deriv]
  · filter_upwards [hq, hg.2.2.2.2, ae_restrict_mem measurableSet_Ioo]
      with x hqx hKx hx
    have hsource := mul_nonpos_of_nonneg_of_nonpos (hfpos x hx).le hqx
    have hpotential := mul_le_mul_of_nonneg_right hKx.2
      (mul_nonneg (hfpos x hx).le (hnonneg x hx))
    nlinarith only [hsource, hpotential]

end RicciFlowSharpEstimate.Geometry.AreaProfile
