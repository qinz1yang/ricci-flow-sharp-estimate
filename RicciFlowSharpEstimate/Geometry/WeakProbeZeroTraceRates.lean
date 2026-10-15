/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeBoundaryUniqueness
import RicciFlowSharpEstimate.Geometry.AreaPrimitivePoleRates
import RicciFlowSharpEstimate.Analysis.PolarFluxLeadingRates

/-! # Nonzero leading rates at zero-trace physical poles of the actual minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem zero_mul_bounded {α : Type*} {l : Filter α} {u v : α → ℝ} {B : ℝ}
    (hu : Tendsto u l (𝓝 0)) (hv : ∀ᶠ x in l, |v x| ≤ B) :
    Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hv] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simpa only [norm_zero, zero_mul, Real.norm_eq_abs] using hu.norm.mul_const B

/-- If an actual minimizing probe has zero trace at a physical pole, its
canonical operator has a nonzero trace and the same probe has the displayed
linear leading term. The right derivative has the genuine tail-integral sign.
No source orientation, curvature trace or polar nondegeneracy is assumed. -/
theorem IsRecoverableAreaCompetitor.probe_zero_trace_leading_rates_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let f := warp K
    let b := warpSlope K
    let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x /
      f x ^ 2
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    ∃ qL qR : ℝ,
      Tendsto (fun x => q x + r x * (2 - b x) / (2 * f x)) (𝓝[>] 0) (𝓝 qL) ∧
      Tendsto (fun x => q x + r x * (2 + b x) / (2 * f x)) (𝓝[<] 1) (𝓝 qR) ∧
      (R 0 = 0 → qL ≠ 0 ∧ Tendsto q (𝓝[>] 0) (𝓝 qL) ∧
        Tendsto p (𝓝[>] 0) (𝓝 (qL / 4)) ∧
        Tendsto (fun x => r x / x) (𝓝[>] 0) (𝓝 (qL / 4))) ∧
      (R 1 = 0 → qR ≠ 0 ∧ Tendsto q (𝓝[<] 1) (𝓝 qR) ∧
        Tendsto p (𝓝[<] 1) (𝓝 (-qR / 4)) ∧
        Tendsto (fun x => r x / (1 - x)) (𝓝[<] 1) (𝓝 (qR / 4))) := by
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x / f x ^ 2
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let F := weakProbeDerivativeFlux K p
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  obtain ⟨qL, qR, _, _, hQL, hQR, _⟩ :=
    h.probe_bounded_polar_states_of_minimum hC hr hp hmin
  obtain ⟨_, _, _, _, _, hrL, hrR, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  obtain ⟨hrD, _, _, hQeq, _, _⟩ := h.probe_first_order_system_of_minimum hC hr hp hmin
  obtain ⟨hFAC, hF0, hF1, hFD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  have hFDq : ∀ᵐ x ∂areaμ, HasDerivAt F (f x * (q x + K x * r x)) x := by
    filter_upwards [hFD, hQeq] with x hx he
    simpa only [he] using hx
  have hKB : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hratio := h.primitive_polar_ratio_bounds hC
  have hwarp := h.primitive_first_order_pole_rates hC
  have hnonzero := h.probe_pole_state_nonzero_of_minimum hC hr hp hmin
  refine ⟨qL, qR, hQL, hQR, ?_, ?_⟩
  · intro hR0
    have hr0 : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [hR0] using hrL
    have hc : Tendsto (fun x => r x * (2 - b x) / (2 * f x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hh := (zero_mul_bounded hr0 (by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
        exact (hratio.1 x hx).2)).div_const 2
      apply (show Tendsto (fun x => (r x * ((2 - b x) / f x)) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) from by simpa only [zero_div] using hh).congr'
      filter_upwards [] with x
      ring
    have hqL : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 qL) := by
      apply (show Tendsto (fun x => (q x + r x * (2 - b x) / (2 * f x)) -
        r x * (2 - b x) / (2 * f x)) (𝓝[>] (0 : ℝ)) (𝓝 qL) from
        by simpa only [sub_zero] using hQL.sub hc).congr'
      filter_upwards [] with x
      ring
    have hn : qL ≠ 0 := by
      intro he
      exact hnonzero.1 hr0 (by simpa only [he] using hqL)
    have hrate := Analysis.leading_rates_of_degenerate_derivative_flux
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ) ≠ 0) hFAC hF0 hFDq
      (fun _ _ => rfl) hwarp.1 hKB hr0 hqL hrD
    exact ⟨hn, hqL, by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hrate⟩
  · intro hR1
    have hr1 : Tendsto r (𝓝[<] (1 : ℝ)) (𝓝 0) := by simpa only [hR1] using hrR
    have hc : Tendsto (fun x => r x * (2 + b x) / (2 * f x))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hh := (zero_mul_bounded hr1 (by
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
        exact (hratio.2 x hx).2)).div_const 2
      apply (show Tendsto (fun x => (r x * ((2 + b x) / f x)) / 2)
        (𝓝[<] (1 : ℝ)) (𝓝 0) from by simpa only [zero_div] using hh).congr'
      filter_upwards [] with x
      ring
    have hqR : Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 qR) := by
      apply (show Tendsto (fun x => (q x + r x * (2 + b x) / (2 * f x)) -
        r x * (2 + b x) / (2 * f x)) (𝓝[<] (1 : ℝ)) (𝓝 qR) from
        by simpa only [sub_zero] using hQR.sub hc).congr'
      filter_upwards [] with x
      ring
    have hn : qR ≠ 0 := by
      intro he
      exact hnonzero.2 hr1 (by simpa only [he] using hqR)
    have hrate := Analysis.leading_rates_of_degenerate_derivative_flux_right
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ) ≠ 0) hFAC hF1 hFDq
      (fun _ _ => rfl) hwarp.2 hKB hr1 hqR hrD
    exact ⟨hn, hqR, by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hrate⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
