/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbePoleTraces
import RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem
import RicciFlowSharpEstimate.Geometry.AreaSlopePoleBounds

/-! # The actual curvature-cancelled polar Euler fluxes -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Both corrected fluxes are genuine globally AC functions with the appropriate
zero pole value. Their complete derivatives contain a pole-distance factor;
no derivative or endpoint limit of measurable curvature is used. -/
theorem IsRecoverableAreaCompetitor.polar_corrected_flux_derivatives_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let f := warp K
    let b := warpSlope K
    let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
    let P := weakProbeEulerFlux K r p z lam
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    let EL := fun x => P x - (2 - b x) * b x * R x / 2
    let ER := fun x => P x - (2 + b x) * b x * R x / 2
    let T := fun u x => f x * K x * (q x - K x * r x) +
      b x * (f x * K x - u x) * p x / 2 + K x * u x ^ 2 * r x / 2 +
        lam * f x * r x
    AbsolutelyContinuousOnInterval EL 0 1 ∧ AbsolutelyContinuousOnInterval ER 0 1 ∧
      EL 0 = 0 ∧ ER 1 = 0 ∧
      (∀ᵐ x ∂areaμ, HasDerivAt EL (T (fun x => 2 - b x) x) x ∧
        HasDerivAt ER (T (fun x => 2 + b x) x) x) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let P := weakProbeEulerFlux K r p z lam
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let EL := fun x => P x - (2 - b x) * b x * R x / 2
  let ER := fun x => P x - (2 + b x) * b x * R x / 2
  have hg := h.geometry_bounds hC
  have hbAC := (h.slope_pole_quotient_bounds hC).1
  obtain ⟨_, _, hRAC, hReq, hRD, _, _, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  have hEuler := h.probe_euler_flux_of_minimum hC hmin
  have hPAC := hEuler.2.1
  have hP0 := hEuler.2.2.2.1
  have hP1 := hEuler.2.2.2.2.1
  have hcCD : ContDiffOn ℝ 1 (fun _ : ℝ => (2 : ℝ)) (uIcc (0 : ℝ) 1) :=
    contDiff_const.contDiffOn
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (2 : ℝ)) 0 1 :=
    hcCD.absolutelyContinuousOnInterval
  have hEL := hPAC.fun_sub ((((hc.fun_sub hbAC).fun_mul hbAC).fun_mul hRAC).const_mul
    (1 / 2 : ℝ))
  have hER := hPAC.fun_sub ((((hc.fun_add hbAC).fun_mul hbAC).fun_mul hRAC).const_mul
    (1 / 2 : ℝ))
  have hELAC : AbsolutelyContinuousOnInterval EL 0 1 := by
    apply hEL.congr
    intro x _
    dsimp only [EL, P, b, R, lam]
    ring
  have hERAC : AbsolutelyContinuousOnInterval ER 0 1 := by
    apply hER.congr
    intro x _
    dsimp only [ER, P, b, R, lam]
    ring
  refine ⟨hELAC, hERAC, ?_, ?_, ?_⟩
  · dsimp only [EL, b, P, lam]
    rw [hg.2.2.2.1.2.2.1, hP0]
    ring
  · dsimp only [ER, b, P, lam]
    rw [hg.2.2.2.1.2.2.2, hP1]
    ring
  · have hsys := (h.probe_first_order_system_of_minimum hC hr hp hmin).2.2.2.2.2
    filter_upwards [hsys, (h.primitive_local_regularity hC).2.2,
      ae_restrict_mem measurableSet_Ioo] with x hx hbD hxI
    have hR := hRD x hxI
    have hEq := hReq hxI
    dsimp only at hEq
    have hPD := hx.2.2
    have hL := hPD.fun_sub
      (((((hasDerivAt_const x (2 : ℝ)).fun_sub hbD).fun_mul hbD).fun_mul hR).div_const 2)
    have hU := hPD.fun_sub
      (((((hasDerivAt_const x (2 : ℝ)).fun_add hbD).fun_mul hbD).fun_mul hR).div_const 2)
    constructor
    · change HasDerivAt EL _ x at hL
      apply hL.congr_deriv
      rw [hEq]
      ring
    · change HasDerivAt ER _ x at hU
      apply hU.congr_deriv
      rw [hEq]
      ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
