/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.IntegrableDerivativeExtension
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic endpoint remainders from an essential second-derivative limit

Local absolute continuity of the genuine first derivative and its finite
endpoint trace suffice for two endpoint integrations. Neither raw endpoint
assignment is identified with a trace without a proved limiting equation.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set Topology

/-- A genuine derivative with local absolute continuity and an essential
derivative limit gives the quadratic endpoint remainder, using the actual
finite traces of the function and its first derivative. -/
theorem tendsto_quadratic_remainder_of_ae_second_derivative_limit
    {H V A : ℝ → ℝ} {b h0 h1 L : ℝ} (hb : 0 < b)
    (hHD : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt H (V x) x)
    (hVAC : ∀ a ∈ Ioo (0 : ℝ) b, ∀ c ∈ Ioo (0 : ℝ) b,
      AbsolutelyContinuousOnInterval V a c)
    (hVD : ∀ᵐ x ∂volume.restrict (Ioo 0 b), HasDerivAt V (A x) x)
    (hH0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 h0))
    (hV0 : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 h1))
    (hA0 : Tendsto A ((𝓝[>] (0 : ℝ)) ⊓ ae volume) (𝓝 L)) :
    Tendsto (fun x => (H x - h0 - h1 * x) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun x => |A x - L|)
      ((𝓝[>] (0 : ℝ)) ⊓ ae volume) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hA0.sub_const L).abs
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.eventually_inf.mp
    (herror.eventually (gt_mem_nhds hε))
  obtain ⟨d, hd, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hU
  let δ := min b d / 2
  have hδ : 0 < δ := div_pos (lt_min hb hd) (by norm_num)
  have hδb : δ < b := by
    dsimp only [δ]
    linarith [min_le_left b d, lt_min hb hd]
  have hδd : δ < d := by
    dsimp only [δ]
    linarith [min_le_right b d, lt_min hb hd]
  have hsub : Ioo (0 : ℝ) δ ⊆ Ioo (0 : ℝ) b :=
    fun _ hx => ⟨hx.1, hx.2.trans hδb⟩
  have hVDδ : ∀ᵐ x ∂volume.restrict (Ioo 0 δ), HasDerivAt V (A x) x :=
    ae_restrict_of_ae_restrict_of_subset hsub hVD
  have hAM : AEStronglyMeasurable A (volume.restrict (Ioo 0 δ)) := by
    apply (stronglyMeasurable_deriv V).aestronglyMeasurable.congr
    filter_upwards [hVDδ] with x hx
    exact hx.deriv
  have herr : ∀ᵐ x ∂volume.restrict (Ioo 0 δ), |A x - L| ≤ ε := by
    filter_upwards [ae_restrict_of_ae hW, ae_restrict_mem measurableSet_Ioo] with x hxW hx
    exact (hUW x ⟨hlocal ⟨hx.1, hx.2.trans hδd⟩, hxW⟩).le
  have hAI : IntegrableOn A (Ioo 0 δ) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => |L| + ε) (Ioo 0 δ) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp intervalIntegrable_const
    apply hconst.mono' hAM
    filter_upwards [herr] with x hx
    rw [Real.norm_eq_abs]
    calc
      |A x| = |(A x - L) + L| := by rw [sub_add_cancel]
      _ ≤ |A x - L| + |L| := abs_add_le _ _
      _ ≤ |L| + ε := by linarith
  have hAII : IntervalIntegrable A volume 0 δ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mpr hAI
  obtain ⟨G, hGAC, hGeq, hGlim, _, _⟩ := exists_boundary_extension_of_integrable_deriv hδ
    (fun a ha c hc => hVAC a (hsub ha) c (hsub hc)) hVDδ hAI
  have hG0 : G 0 = h1 := tendsto_nhds_unique hGlim hV0
  have hDG : ∀ᵐ x ∂volume.restrict (Ioo 0 δ), HasDerivAt G (A x) x := by
    filter_upwards [hVDδ, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    apply hx.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
    exact hGeq hy
  have hVI : IntervalIntegrable V volume 0 δ := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mpr
    have hGI : IntegrableOn G (Ioo 0 δ) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp
        hGAC.continuousOn.intervalIntegrable
    exact hGI.congr_fun hGeq measurableSet_Ioo
  have hjoin (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) :
      uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) δ := by
    rw [uIcc_of_le hx.1.le, uIcc_of_le hδ.le]
    exact Icc_subset_Icc le_rfl hx.2.le
  have hVFTC (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) :
      (∫ t in 0..x, A t) = V x - h1 := by
    calc
      (∫ t in 0..x, A t) = ∫ t in 0..x, deriv G t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_imp_of_ae_restrict hDG] with t ht htI
        have ht' : t ∈ Ioc (0 : ℝ) x := by
          simpa only [uIoc_of_le hx.1.le] using htI
        exact (ht ⟨ht'.1, ht'.2.trans_lt hx.2⟩).deriv.symm
      _ = G x - G 0 := (hGAC.mono (hjoin x hx)).integral_deriv_eq_sub
      _ = V x - h1 := by rw [hGeq hx, hG0]
  have hHFTC (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) :
      (∫ t in 0..x, V t) = H x - h0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx.1
      (fun t ht => hHD t (hsub ⟨ht.1, ht.2.trans hx.2⟩))
      (hVI.mono_set (hjoin x hx)) hH0
    exact (hHD x (hsub hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hVbound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) :
      |V x - h1 - L * x| ≤ ε * x := by
    have heq : (∫ t in 0..x, A t - L) = V x - h1 - L * x := by
      rw [intervalIntegral.integral_sub (hAII.mono_set (hjoin x hx))
        intervalIntegrable_const, hVFTC x hx, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := fun t => A t - L) (a := 0) (b := x) (C := ε) (by
        filter_upwards [ae_imp_of_ae_restrict herr] with t ht htI
        have ht' : t ∈ Ioc (0 : ℝ) x := by
          simpa only [uIoc_of_le hx.1.le] using htI
        simpa only [Real.norm_eq_abs] using ht ⟨ht'.1, ht'.2.trans_lt hx.2⟩)
    simpa only [Real.norm_eq_abs, heq, sub_zero, abs_of_pos hx.1] using hnorm
  filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
  have hVIx := hVI.mono_set (hjoin x hx)
  have hlinI : IntervalIntegrable (fun t : ℝ => L * t) volume 0 x :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 x
  have hInt : (∫ t in 0..x, V t - h1 - L * t) =
      H x - h0 - h1 * x - L * x ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (hVIx.sub intervalIntegrable_const) hlinI,
      intervalIntegral.integral_sub hVIx intervalIntegrable_const, hHFTC x hx,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hdom : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) x →
      ‖V t - h1 - L * t‖ ≤ ε * t := by
    filter_upwards [] with t ht
    simpa only [Real.norm_eq_abs] using hVbound t ⟨ht.1, ht.2.trans_lt hx.2⟩
  have hquad : |H x - h0 - h1 * x - L * x ^ 2 / 2| ≤ ε * x ^ 2 / 2 := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le hx.1.le hdom
      ((continuous_const.mul continuous_id).intervalIntegrable 0 x)
    have heval : (∫ t in 0..x, ε * t) = ε * x ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    simpa only [Real.norm_eq_abs, hInt, heval] using hn
  have hquot : (H x - h0 - h1 * x) / x ^ 2 - L / 2 =
      (H x - h0 - h1 * x - L * x ^ 2 / 2) / x ^ 2 := by
    field_simp [hx.1.ne']
  rw [Real.dist_eq, hquot, abs_div, abs_of_pos (sq_pos_of_pos hx.1)]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply (div_le_iff₀ (sq_pos_of_pos hx.1)).mpr
  calc
    |H x - h0 - h1 * x - L * x ^ 2 / 2| ≤ ε * x ^ 2 / 2 := hquad
    _ = ε / 2 * x ^ 2 := by ring

end RicciFlowSharpEstimate.Analysis
