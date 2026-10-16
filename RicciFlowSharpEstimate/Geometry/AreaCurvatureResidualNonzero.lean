/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakCurvatureZeroTracePole
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice

/-! # Nonvanishing of the complete centered curvature residual -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem continuous_le_of_ae_le {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Ioo (0 : ℝ) 1))
    (hv : ContinuousOn v (Ioo (0 : ℝ) 1))
    (h : ∀ᵐ x ∂areaμ, u x ≤ v x) : ∀ x ∈ Ioo (0 : ℝ) 1, u x ≤ v x := by
  have he : (fun x => max (u x - v x) 0) =ᵐ[areaμ] (fun _ => (0 : ℝ)) := by
    filter_upwards [h] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have hc : ContinuousOn (fun x => max (u x - v x) 0) (Ioo (0 : ℝ) 1) :=
    (hu.sub hv).sup continuousOn_const
  have hz := Measure.eqOn_open_of_ae_eq he isOpen_Ioo hc continuousOn_const
  intro x hx
  exact sub_nonpos.mp ((le_max_left (u x - v x) 0).trans (le_of_eq (hz hx)))

private theorem tendsto_zero_of_abs_bound {α : Type*} {l : Filter α}
    {u v : α → ℝ} {M : ℝ}
    (hb : ∀ᶠ x in l, |u x| ≤ M * |v x|) (hv : Tendsto v l (𝓝 0)) :
    Tendsto u l (𝓝 0) := by
  apply squeeze_zero_norm'
  · simpa only [Real.norm_eq_abs] using hb
  · simpa only [abs_zero, mul_zero] using hv.abs.const_mul M

private theorem quadratic_remainder_not_cubic_bound {H D : ℝ → ℝ} {L A δ M : ℝ}
    (hA : A ≠ 0)
    (hH : Tendsto (fun x => (H x - L * x) / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hD : Tendsto (fun x => D x / x ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 δ))
    (hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), |H x| ≤ M * |D x|) : False := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hD2 : Tendsto (fun x => D x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := hD.mul hx0
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    field_simp [hx.ne']
  have hb2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), |H x / x ^ 2| ≤ M * |D x / x ^ 2| := by
    filter_upwards [hb, self_mem_nhdsWithin] with x hx hx0
    change 0 < x at hx0
    rw [abs_div, abs_div, abs_of_pos (sq_pos_of_pos hx0)]
    calc
      |H x| / x ^ 2 ≤ (M * |D x|) / x ^ 2 :=
        div_le_div_of_nonneg_right hx (sq_nonneg x)
      _ = M * (|D x| / x ^ 2) := by ring
  have hH2 := tendsto_zero_of_abs_bound hb2 hD2
  have hL : L = 0 := by
    have hh := (hH2.sub hH).mul hx0
    simp only [mul_zero] at hh
    have hc : Tendsto (fun _ : ℝ => L) (𝓝[>] 0) (𝓝 0) := by
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      field_simp [hx.ne']
      ring
    exact tendsto_nhds_unique tendsto_const_nhds hc
  have hHA : Tendsto (fun x => H x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa only [hL, zero_mul, sub_zero] using hH
  have he : A = 0 := tendsto_nhds_unique hHA hH2
  exact hA he

/-- No centered moment multiplier makes the complete curvature residual of
an actual zero-action global minimum vanish almost everywhere. The argument
uses the actual two-pole values and nonzero quadratic zero-trace rate;
no continuity of the full residual or source orientation is assumed. -/
theorem IsRecoverableAreaCompetitor.curvature_centered_residual_ne_zero_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (t : ℝ) :
    ¬ (fun x => weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ)))
      =ᵐ[areaμ] (fun _ => 0) := by
  intro hZ
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let H := fun x => weakCurvatureAdjointRegularPart K r p z 0 x - t * (x - 1 / 2)
  let D := fun x => 2 * warp K x * r x ^ 2
  have hg := h.geometry_bounds hC
  have hReg := h.curvature_adjoint_regularPart_of_minimum hC hr hp hmin
  dsimp only at hReg
  rw [hzero] at hReg
  have hHc : ContinuousOn H (Ioo (0 : ℝ) 1) :=
    hReg.2.1.continuousOn.sub (continuous_const.mul
      (continuous_id.sub continuous_const)).continuousOn
  have hDc : ContinuousOn D (Ioo (0 : ℝ) 1) :=
    (continuousOn_const.mul (hg.1.mono Ioo_subset_Icc_self)).mul (hr.pow 2)
  have hKB : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hbAE : ∀ᵐ x ∂areaμ, |H x| ≤ (2 * C) * |D x| := by
    filter_upwards [hReg.1, hZ, hKB] with x hx hzx hKx
    have he : H x = -(D x * K x) := by
      dsimp only [H, D]
      change weakCurvatureAdjoint K r p z 0 x =
        2 * warp K x * r x ^ 2 * K x + weakCurvatureAdjointRegularPart K r p z 0 x at hx
      change weakCurvatureAdjoint K r p z 0 x - t * (x - 1 / 2) = 0 at hzx
      linarith
    rw [he, abs_neg, abs_mul]
    calc
      |D x| * |K x| ≤ |D x| * (2 * C) := mul_le_mul_of_nonneg_left hKx (abs_nonneg _)
      _ = (2 * C) * |D x| := mul_comm _ _
  have hb : ∀ x ∈ Ioo (0 : ℝ) 1, |H x| ≤ (2 * C) * |D x| :=
    continuous_le_of_ae_le hHc.abs (continuousOn_const.mul hDc.abs) hbAE
  have hLD : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hRD : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨_, _, _, _, _, hrL, hrR, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  change Tendsto r (𝓝[>] 0) (𝓝 (R 0)) at hrL
  change Tendsto r (𝓝[<] 1) (𝓝 (R 1)) at hrR
  have hfL : Tendsto (warp K) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hg.2.2.2.1.1] using
      ((hg.1.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hfR : Tendsto (warp K) (𝓝[<] 1) (𝓝 0) := by
    simpa only [hg.2.2.2.1.2.1] using
      ((hg.1.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT zero_lt_one)).tendsto
  have hDL : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hfL.const_mul 2).mul (hrL.pow 2)
  have hDR : Tendsto D (𝓝[<] 1) (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hfR.const_mul 2).mul (hrR.pow 2)
  have hHL0 := tendsto_zero_of_abs_bound (hLD.mono fun x hx => hb x hx) hDL
  have hHR0 := tendsto_zero_of_abs_bound (hRD.mono fun x hx => hb x hx) hDR
  have hTraces := h.curvature_adjoint_pole_traces_of_minimum hC hr hp hmin
  dsimp only at hTraces
  rw [hzero] at hTraces
  have hVL : -2 * R 0 ^ 2 + t / 2 = 0 :=
    tendsto_nhds_unique ((hTraces.2.2 t).1) hHL0
  have hVR : -2 * R 1 ^ 2 - t / 2 = 0 :=
    tendsto_nhds_unique ((hTraces.2.2 t).2) hHR0
  have hR0sq : R 0 ^ 2 = 0 := by nlinarith [sq_nonneg (R 0), sq_nonneg (R 1)]
  have hR0 : R 0 = 0 := sq_eq_zero_iff.mp hR0sq
  have ht : t = 0 := by rw [hR0] at hVL; nlinarith
  have hQuad0 := h.curvature_adjoint_zero_trace_quadratic_pole_rates_of_minimum
    hC hr hp hmin
  dsimp only at hQuad0
  rw [hzero] at hQuad0
  simp only [zero_mul, sub_zero] at hQuad0
  obtain ⟨qL, qR, _, _, hQuad⟩ := hQuad0
  have hc := (hQuad t).1 hR0
  let L := 2 * (∫ s in (0 : ℝ)..1, (1 - s) * weakCurvatureWarpCoefficient K r p z s) -
    2 * (∫ s in (0 : ℝ)..1, weakCurvatureSlopeCoefficient K r p z s) - t
  have hrem := hc.2.2.2.2
  change Tendsto (fun x => (H x - t / 2 - L * x) / x ^ 2)
    (𝓝[>] (0 : ℝ)) (𝓝 (-3 * qL ^ 2 / 8)) at hrem
  have ht2 : t / 2 = 0 := by rw [ht]; norm_num
  simp only [ht2, sub_zero] at hrem
  exact quadratic_remainder_not_cubic_bound
    (by nlinarith only [sq_pos_of_ne_zero hc.1] : -3 * qL ^ 2 / 8 ≠ 0)
    hrem hc.2.2.1 (hLD.mono fun x hx => hb x hx)

end RicciFlowSharpEstimate.Geometry.AreaProfile
