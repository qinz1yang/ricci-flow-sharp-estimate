/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeWeightedPoleTraces
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjointRegularity
import RicciFlowSharpEstimate.Analysis.GreenBoundaryTraces

/-! # The actual complete regular-adjoint traces at both physical poles -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem closed_interval_pole_limits {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (0 : ℝ) 1)) :
    Tendsto u (𝓝[>] 0) (𝓝 (u 0)) ∧ Tendsto u (𝓝[<] 1) (𝓝 (u 1)) := by
  exact ⟨((hu.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGT zero_lt_one)).tendsto,
    ((hu.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT zero_lt_one)).tendsto⟩

/-- The canonical complete regular adjoint has the genuine two physical pole
limits, including the full Green and mass correction. The same explicit probe
extension fixes both values; its traces may vanish. Centering uses any one
fixed multiplier t, so subsequent scale-box consumers keep their chosen t. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_pole_traces_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    let W := weakCurvatureAdjointRegularPart K r p z (weakMeridionalAction K r p z)
    Tendsto W (𝓝[>] 0) (𝓝 (-2 * R 0 ^ 2)) ∧
      Tendsto W (𝓝[<] 1) (𝓝 (-2 * R 1 ^ 2)) ∧
      ∀ t : ℝ,
        Tendsto (fun x => W x - t * (x - 1 / 2)) (𝓝[>] 0)
          (𝓝 (-2 * R 0 ^ 2 + t / 2)) ∧
        Tendsto (fun x => W x - t * (x - 1 / 2)) (𝓝[<] 1)
          (𝓝 (-2 * R 1 ^ 2 - t / 2)) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let G := fun x => ∫ s, Analysis.unitDirichletKernel s x * A s ∂areaμ
  let T := fun x => ∫ s, Analysis.unitDirichletSlopeKernel s x * B s ∂areaμ
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let W := weakCurvatureAdjointRegularPart K r p z lam
  have hg := h.geometry_bounds hC
  obtain ⟨_, _, _, _, _, hrLT, hrRT, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  change Tendsto r (𝓝[>] 0) (𝓝 (R 0)) at hrLT
  change Tendsto r (𝓝[<] 1) (𝓝 (R 1)) at hrRT
  obtain ⟨_, _, hpLT, hpRT, hqLT, hqRT⟩ :=
    h.probe_weighted_state_pole_traces_of_minimum hC hp hmin
  change Tendsto (fun x => f x * p x) (𝓝[>] 0) (𝓝 0) at hpLT
  change Tendsto (fun x => f x * p x) (𝓝[<] 1) (𝓝 0) at hpRT
  change Tendsto (fun x => f x * q x) (𝓝[>] 0) (𝓝 0) at hqLT
  change Tendsto (fun x => f x * q x) (𝓝[<] 1) (𝓝 0) at hqRT
  have hbLimits := closed_interval_pole_limits hg.2.1
  have hbLT : Tendsto b (𝓝[>] 0) (𝓝 2) := by
    simpa only [b, hg.2.2.2.1.2.2.1] using hbLimits.1
  have hbRT : Tendsto b (𝓝[<] 1) (𝓝 (-2)) := by
    simpa only [b, hg.2.2.2.1.2.2.2] using hbLimits.2
  obtain ⟨_, hAw0, hBi, _⟩ := h.curvature_coefficients_integrable hC
  have hweightM : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hweightB : ∀ᵐ x ∂areaμ, ‖x * (1 - x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  have hAw : Integrable (fun x => x * (1 - x) * A x) areaμ := by
    apply (hAw0.sub ((h.2.1.integrable_sq.bdd_mul hweightM hweightB).const_mul lam)).congr
    filter_upwards [] with x
    change x * (1 - x) * weakCurvatureWarpCoefficient K r p z x -
      lam * (x * (1 - x) * r x ^ 2) = x * (1 - x) * A x
    dsimp only [A]
    ring
  obtain ⟨hGC, hG0, hG1⟩ := Analysis.weighted_dirichlet_adjoint_boundary_traces A hAw
  obtain ⟨_, hTAC, hT0, hT1, _⟩ := Analysis.slope_kernel_adjoint_absolutelyContinuous B hBi
  have hTC : ContinuousOn T (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hTAC.continuousOn
  have hGL := closed_interval_pole_limits hGC
  change T 0 = 0 at hT0
  change T 1 = 0 at hT1
  have hTL := closed_interval_pole_limits hTC
  have hGLT : Tendsto G (𝓝[>] 0) (𝓝 0) := by simpa only [hG0] using hGL.1
  have hGRT : Tendsto G (𝓝[<] 1) (𝓝 0) := by simpa only [hG1] using hGL.2
  have hTLT : Tendsto T (𝓝[>] 0) (𝓝 0) := by simpa only [hT0] using hTL.1
  have hTRT : Tendsto T (𝓝[<] 1) (𝓝 0) := by simpa only [hT1] using hTL.2
  have hW : W = fun x => -2 * (f x * q x) * r x - b x * r x * (f x * p x) -
      b x ^ 2 * r x ^ 2 / 2 + 2 * G x + 2 * T x := by
    funext x
    dsimp only [W, weakCurvatureAdjointRegularPart, f, b, q, A, B, G, T, lam]
    ring
  have hWL : Tendsto W (𝓝[>] 0) (𝓝 (-2 * R 0 ^ 2)) := by
    rw [hW]
    convert (((((hqLT.const_mul (-2)).mul hrLT).sub ((hbLT.mul hrLT).mul hpLT)).sub
      (((hbLT.pow 2).mul (hrLT.pow 2)).div_const 2)).add
        (hGLT.const_mul 2)).add (hTLT.const_mul 2) using 1
    congr 1
    ring
  have hWR : Tendsto W (𝓝[<] 1) (𝓝 (-2 * R 1 ^ 2)) := by
    rw [hW]
    convert (((((hqRT.const_mul (-2)).mul hrRT).sub ((hbRT.mul hrRT).mul hpRT)).sub
      (((hbRT.pow 2).mul (hrRT.pow 2)).div_const 2)).add
        (hGRT.const_mul 2)).add (hTRT.const_mul 2) using 1
    congr 1
    ring
  refine ⟨hWL, hWR, ?_⟩
  intro t
  have hIL : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hIR : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  constructor
  · convert hWL.sub ((hIL.sub_const (1 / 2 : ℝ)).const_mul t) using 1
    congr 1
    dsimp only [R]
    ring
  · convert hWR.sub ((hIR.sub_const (1 / 2 : ℝ)).const_mul t) using 1
    congr 1
    dsimp only [R]
    ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
