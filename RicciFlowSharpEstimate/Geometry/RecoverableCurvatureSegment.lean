/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence
import RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra

/-!
# Feasible normalized curvature segments in the recoverable weak class

The segment toward any admissible smooth curvature keeps the two exact
moments and actual positive ratio witnesses. Applying that same segment to
the recovery curvatures, followed by literal positive mass normalization,
constructs the required smooth recovery for the varied weak pair.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Positive admissible curvature preserves strictly positive mass of a
unit-mass weak probe throughout every convex curvature segment. This is
proved from the actual common warp comparisons, not supplied to the
normalization theorem as an extra premise. -/
theorem IsRecoverableAreaCompetitor.probeMass_curvature_segment_pos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (J : ℝ → ℝ) (hJ : IsSmoothAreaCurvature C J)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < probeMass (fun x => (1 - t) * K x + t * J x) r := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGeo := h.geometry_bounds hC
  have hMK : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.exists_action_recovery hC).2.1
  have hfJ : AEStronglyMeasurable (warp J) areaμ :=
    (warp_continuous J hJ.1.continuous).aestronglyMeasurable
  have hfJbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp J x ∧ warp J x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := hJ.geometry_bounds x ⟨hx.1.le, hx.2.le⟩
    refine ⟨?_, by simpa only [mul_assoc] using hg.2.1⟩
    exact (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hg.1
  have hMJ := probeMass_intervalIntegrable_of_warp_bounds J r (2 * C)
    h.2.1.memLp (by positivity) hfJ hfJbox
  have hwarp (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      warp K x ≤ C ^ 2 * warp J x := by
    calc
      warp K x ≤ (2 * C) * x * (1 - x) := (hGeo.2.2.1 x hx).2.1
      _ = C ^ 2 * ((2 / C) * x * (1 - x)) := by field_simp [hCpos.ne']
      _ ≤ C ^ 2 * warp J x :=
        mul_le_mul_of_nonneg_left (hJ.geometry_bounds x hx).1 (sq_nonneg C)
  have hMassLe : probeMass K r ≤ C ^ 2 * probeMass J r := by
    calc
      probeMass K r ≤ ∫ x in (0 : ℝ)..1, C ^ 2 * (warp J x * r x ^ 2) := by
        apply intervalIntegral.integral_mono_on zero_le_one hMK (hMJ.const_mul (C ^ 2))
        intro x hx
        calc
          warp K x * r x ^ 2 ≤ (C ^ 2 * warp J x) * r x ^ 2 :=
            mul_le_mul_of_nonneg_right (hwarp x hx) (sq_nonneg _)
          _ = _ := by ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hmJ : 0 < probeMass J r := by
    rw [h.2.2.2.2.2.1] at hMassLe
    by_contra hnot
    have hnon : probeMass J r ≤ 0 := le_of_not_gt hnot
    have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg C) hnon
    linarith
  rw [probeMass_affine_curvature_of_integrableOn K J r
    (h.1.integrable (by norm_num)) (hJ.memLp_curvature.integrable (by norm_num)) hMK hMJ t]
  by_cases hlt : t < 1
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hlt) (by rw [h.2.2.2.2.2.1]; exact zero_lt_one))
      (mul_nonneg ht.1 hmJ.le)
  · have htone : t = 1 := le_antisymm ht.2 (not_lt.mp hlt)
    simpa only [htone, sub_self, zero_mul, one_mul, zero_add] using hmJ

/-- A convex segment toward an arbitrary admissible original smooth
curvature, with the same probe, gives a normalized recoverable competitor
with strictly positive actual physical mass. Original ratio witnesses
are mixed along with the curvatures; no common fixed box is assumed. -/
theorem IsRecoverableAreaCompetitor.normalized_curvature_segment
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (J : ℝ → ℝ) (hJ : IsSmoothAreaCurvature C J)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsRecoverableAreaCompetitor C (fun x => (1 - t) * K x + t * J x)
      (normalizedProbe (fun x => (1 - t) * K x + t * J x) r)
      (fun x => (1 / Real.sqrt (probeMass (fun y => (1 - t) * K y + t * J y) r)) * p x)
      (fun x => (1 / Real.sqrt (probeMass (fun y => (1 - t) * K y + t * J y) r)) * z x) := by
  have hm := h.probeMass_curvature_segment_pos hC J hJ t ht
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKmem : MemLp K 2 areaμ := h.1
  have hJmem : MemLp J 2 areaμ := hJ.memLp_curvature
  have hgraph := h.2.1
  let Kt : ℝ → ℝ := fun x => (1 - t) * K x + t * J x
  let β : ℝ := 1 / Real.sqrt (probeMass Kt r)
  have hKtMem : MemLp Kt 2 areaμ :=
    (hKmem.const_mul (1 - t)).add (hJmem.const_mul t)
  have hmom := curvature_moments_affine_of_integrableOn K J
    (hKmem.integrable (by norm_num)) (hJmem.integrable (by norm_num))
    h.2.2.2.1 h.2.2.2.2.1 hJ.2.2.1 hJ.2.2.2 t
  obtain ⟨Ks, rs, hS, hKS, hRS, hPS, hZS, hKae⟩ := h.strong_curvature_subsequence
  let Kn : ℕ → ℝ → ℝ := fun n x => (1 - t) * Ks n x + t * J x
  have hKn (n : ℕ) : IsSmoothAreaCurvature C (Kn n) :=
    (hS n).curvature_admissible.convex_combination hJ t ht
  have hKnt : Tendsto (fun n => eLpNorm (Kn n - Kt) 2 areaμ) atTop (𝓝 0) := by
    have hs := Analysis.strong_L2_const_mul_of_tendsto
      (fun n => (hS n).memLp_curvature) hKmem hKS
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 - t)) atTop (𝓝 (1 - t)))
    apply hs.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    dsimp only [Kn, Kt, Pi.sub_apply]
    ring
  have hKna : ∀ᵐ x ∂areaμ, Tendsto (fun n => Kn n x) atTop (𝓝 (Kt x)) := by
    filter_upwards [hKae] with x hx
    exact (hx.const_mul (1 - t)).add tendsto_const_nhds
  have hL1 : Tendsto (fun n => ∫ x, |Kn n x - Kt x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Kn) (g := Kt) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      (fun n => (hKn n).memLp_curvature) hKtMem (fun _ => hc)
      (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hKnt
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - Kt x|)
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hKtBox : ∀ᵐ x ∂areaμ, 0 ≤ Kt x ∧ Kt x ≤ 2 * C := by
    filter_upwards [hKna, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hlo : 2 / C ≤ Kt x := ge_of_tendsto' hx
      (fun n => ((hKn n).common_bounds x ⟨hxI.1.le, hxI.2.le⟩).1)
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hlo, le_of_tendsto' hx
      (fun n => ((hKn n).common_bounds x ⟨hxI.1.le, hxI.2.le⟩).2)⟩
  have hLimits := action_mass_tendsto_of_strong_area_graph Kn rs Kt r p z
    (2 / C) (2 * C) (by positivity) (fun n => (hKn n).1.continuous)
    (fun n => (hS n).2.1.of_le (by simp)) (fun n => (hKn n).common_bounds)
    (fun n => (hKn n).2.2.1) (fun n => (hKn n).2.2.2)
    (hKtMem.integrable (by norm_num)) hmom.1 hmom.2 hKtBox hgraph
    hL1I hKna hRS hPS hZS
  have hMass : Tendsto (fun n => probeMass (Kn n) (rs n)) atTop
      (𝓝 (probeMass Kt r)) := hLimits.2.2.2
  have hpos : ∀ᶠ n in atTop, 0 < probeMass (Kn n) (rs n) :=
    hMass.eventually (lt_mem_nhds hm)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hmN (n : ℕ) : 0 < probeMass (Kn (n + N)) (rs (n + N)) :=
    hN (n + N) (Nat.le_add_left N n)
  let α : ℕ → ℝ := fun n => 1 / Real.sqrt (probeMass (Kn (n + N)) (rs (n + N)))
  have hα : Tendsto α atTop (𝓝 β) := by
    have hshift := hMass.comp (tendsto_add_atTop_nat N)
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hshift.sqrt (Real.sqrt_pos.mpr hm).ne'
    simpa only [α, β, Function.comp_def, Pi.div_def] using hh
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hS (n + N)).2.1.of_le (by simp)) hgraph hα
    (hRS.comp (tendsto_add_atTop_nat N))
    (hPS.comp (tendsto_add_atTop_nat N))
    (hZS.comp (tendsto_add_atTop_nat N))
  refine ⟨hKtMem, hgraph.const_mul β, ?_, hmom.1, hmom.2,
    probeMass_normalizedProbe Kt r hm, fun n => Kn (n + N),
    fun n => normalizedProbe (Kn (n + N)) (rs (n + N)), ?_,
    hKnt.comp (tendsto_add_atTop_nat N), hNormGraph.1, hNormGraph.2.1, hNormGraph.2.2⟩
  · obtain ⟨κK, ΛK, hκK, hboxK, hratioK⟩ := h.2.2.1
    obtain ⟨κJ, ΛJ, hκJ, hboxJ, hratioJ⟩ := hJ.2.1
    have hw : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hκmix : 0 < (1 - t) * κK + t * κJ := by
      by_cases hlt : t < 1
      · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hκK)
          (mul_nonneg ht.1 hκJ.le)
      · have htone : t = 1 := le_antisymm ht.2 (not_lt.mp hlt)
        simpa only [htone, sub_self, zero_mul, one_mul, zero_add] using hκJ
    refine ⟨(1 - t) * κK + t * κJ, (1 - t) * ΛK + t * ΛJ, hκmix, ?_, ?_⟩
    · filter_upwards [hboxK, ae_restrict_mem measurableSet_Ioo] with x hx hxI
      have hj := hboxJ x ⟨hxI.1.le, hxI.2.le⟩
      exact ⟨add_le_add (mul_le_mul_of_nonneg_left hx.1 hw)
          (mul_le_mul_of_nonneg_left hj.1 ht.1),
        add_le_add (mul_le_mul_of_nonneg_left hx.2 hw)
          (mul_le_mul_of_nonneg_left hj.2 ht.1)⟩
    · apply (div_le_iff₀ hκmix).mpr
      calc
        (1 - t) * ΛK + t * ΛJ ≤ (1 - t) * (C * κK) + t * (C * κJ) :=
          add_le_add (mul_le_mul_of_nonneg_left ((div_le_iff₀ hκK).mp hratioK) hw)
            (mul_le_mul_of_nonneg_left ((div_le_iff₀ hκJ).mp hratioJ) ht.1)
        _ = C * ((1 - t) * κK + t * κJ) := by ring
  · intro n
    exact (hKn (n + N)).with_unit_probe _ (contDiff_const.mul (hS (n + N)).2.1)
      (probeMass_normalizedProbe _ _ (hmN n))

end RicciFlowSharpEstimate.Geometry.AreaProfile
