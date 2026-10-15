/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Endpoint integral averages of actual derivative remainders -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

/-- A remainder tending to zero has interval average tending to zero.
No measurability input is needed for this zero-limit assertion. -/
theorem interval_average_tendsto_zero {u : ℝ → ℝ}
    (hu : Tendsto u (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x => ⨍ t in (0 : ℝ)..x, u t) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), |u x| ≤ ε / 2 := by
    have huabs : Tendsto (fun x => |u x|) (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using hu.abs
    have ht := huabs.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    filter_upwards [ht] with x hx
    simpa only [abs_zero] using hx.le
  obtain ⟨δ, hδ, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
  have hb : |∫ t in (0 : ℝ)..x, u t| ≤ ε / 2 * x := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := u) (a := 0) (b := x) (C := ε / 2) (by
        filter_upwards [] with t ht
        have htI : t ∈ Ioc (0 : ℝ) x := by
          simpa only [uIoc_of_le hx.1.le] using ht
        rw [Real.norm_eq_abs]
        exact hlocal ⟨htI.1, htI.2.trans_lt hx.2⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hx.1] using hh
  rw [Real.dist_eq, sub_zero, interval_average_eq_div, sub_zero,
    abs_div, abs_of_pos hx.1]
  exact ((div_le_iff₀ hx.1).mpr hb).trans_lt (by linarith)

/-- A genuine derivative remainder may be integrated through a finite zero
trace. The comparison source is only L1; derivative integrability near the
endpoint is derived from the finite remainder limit. -/
theorem tendsto_div_sub_interval_average_of_deriv
    {H G : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hH : DifferentiableOn ℝ H (Ioo 0 b))
    (hG : IntegrableOn G (Ioo 0 b))
    (hH0 : Tendsto H (𝓝[>] 0) (𝓝 0))
    (hlim : Tendsto (fun x => deriv H x - G x) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun x => H x / x - (⨍ t in (0 : ℝ)..x, G t)) (𝓝[>] 0) (𝓝 L) := by
  let e := fun x => deriv H x - G x - L
  have he0 : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self] using hlim.sub_const L
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), |e x| ≤ 1 := by
    have heabs : Tendsto (fun x => |e x|) (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using he0.abs
    have ht := heabs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [ht] with x hx
    simpa only [abs_zero] using hx.le
  obtain ⟨d, hd, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let δ := min b d / 2
  have hδ : 0 < δ := div_pos (lt_min hb hd) (by norm_num)
  have hδb : δ < b := by
    have hm := min_le_left b d
    dsimp only [δ]
    linarith [lt_min hb hd]
  have hδd : δ < d := by
    have hm := min_le_right b d
    dsimp only [δ]
    linarith [lt_min hb hd]
  have hsub : Ioo (0 : ℝ) δ ⊆ Ioo (0 : ℝ) b :=
    fun _ hx => ⟨hx.1, hx.2.trans hδb⟩
  have hGs : IntegrableOn G (Ioo (0 : ℝ) δ) := hG.mono_set hsub
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) δ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp intervalIntegrable_const
  have heM : AEStronglyMeasurable e (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ((stronglyMeasurable_deriv H).aestronglyMeasurable.sub
      hGs.aestronglyMeasurable).sub aestronglyMeasurable_const
  have heI : IntegrableOn e (Ioo (0 : ℝ) δ) := by
    apply hOne.mono' heM
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh : |e x| ≤ 1 := hlocal ⟨hx.1, hx.2.trans hδd⟩
    simpa only [Real.norm_eq_abs] using hh
  have hDI : IntegrableOn (deriv H) (Ioo (0 : ℝ) δ) := by
    apply ((heI.add hGs).add (hOne.const_mul L)).congr
    filter_upwards [] with x
    change e x + G x + L * 1 = deriv H x
    dsimp only [e]
    ring
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : HasDerivAt H (deriv H x) x :=
    ((hH x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hmean : Tendsto (fun x => (⨍ t in (0 : ℝ)..x, e t) + L)
      (𝓝[>] 0) (𝓝 L) := by
    simpa only [zero_add] using (interval_average_tendsto_zero he0).add_const L
  apply hmean.congr'
  filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
  have hs : Ioo (0 : ℝ) x ⊆ Ioo (0 : ℝ) δ :=
    fun _ ht => ⟨ht.1, ht.2.trans hx.2⟩
  have hDII : IntervalIntegrable (deriv H) volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr (hDI.mono_set hs)
  have hGII : IntervalIntegrable G volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr (hGs.mono_set hs)
  have hFTC : (∫ t in (0 : ℝ)..x, deriv H t) = H x := by
    simpa only [sub_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx.1
        (fun t ht => hD t (hsub (hs ht))) hDII hH0
        ((hD x (hsub hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  have heInt : (∫ t in (0 : ℝ)..x, e t) =
      H x - (∫ t in (0 : ℝ)..x, G t) - x * L := by
    change (∫ t in (0 : ℝ)..x, (deriv H t - G t) - L) = _
    rw [intervalIntegral.integral_sub (hDII.sub hGII) intervalIntegrable_const,
      intervalIntegral.integral_sub hDII hGII, hFTC, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
  rw [interval_average_eq_div, interval_average_eq_div, sub_zero, heInt]
  field_simp [hx.1.ne']
  ring

end RicciFlowSharpEstimate.Analysis
