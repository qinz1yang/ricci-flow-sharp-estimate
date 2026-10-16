/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaScaleBalancedFreeInterval
import RicciFlowSharpEstimate.Analysis.MomentPreservingBoxExpansion
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCap
import RicciFlowSharpEstimate.Geometry.BoundedCurvatureOptimality
import RicciFlowSharpEstimate.Geometry.AreaGeometricRealization
import RicciFlowSharpEstimate.Geometry.RepresentedRotationalMetric

/-! # Strict cap expansion from an arbitrary zero-action global minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem exists_smooth_negative_pairing
    {C : ℝ} {K r p z J W : ℝ → ℝ}
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hJ : IsBoundedAreaCurvature C J) (hW : Integrable W areaμ)
    (hneg : (∫ x, W x * (J x - K x) ∂areaμ) < 0) :
    ∃ Q : ℝ → ℝ, IsSmoothAreaCurvature C Q ∧
      (∫ x, W x * (Q x - K x) ∂areaμ) < 0 := by
  obtain ⟨κ, Λ, Js, hκ, hb, _, hJs, hJsb, hstrong⟩ := hJ.exists_smooth_recovery
  have hJB : ∀ᵐ x ∂areaμ, |J x| ≤ Λ := by
    filter_upwards [hb] with x hx
    simpa only [abs_of_nonneg (hκ.le.trans hx.1)] using hx.2
  have hJsB (n : ℕ) : ∀ᵐ x ∂areaμ, |Js n x| ≤ Λ :=
    Eventually.of_forall fun x => by
      simpa only [abs_of_nonneg (hκ.le.trans (hJsb n x).1)] using (hJsb n x).2
  have hpair (v : Lp ℝ 2 areaμ) :
      Tendsto (fun n => ∫ x, Js n x * v x ∂areaμ) atTop (𝓝 (∫ x, J x * v x ∂areaμ)) := by
    have hv : Tendsto (fun _ : ℕ => eLpNorm ((fun x => v x) - (fun x => v x)) 2 areaμ)
        atTop (𝓝 0) := by simp only [sub_self, eLpNorm_zero]; exact tendsto_const_nhds
    exact (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun n => (hJs n).memLp_curvature) hJ.memLp_curvature
      (fun _ => Lp.memLp v) (Lp.memLp v) hstrong hv).2.2
  have hJW := Analysis.tendsto_integral_mul_of_bounded_L2_pairings
    (fun n => (hJs n).1.continuous.aestronglyMeasurable) hJ.1 hJsB hJB hpair W hW
  have hWK : Integrable (fun x => W x * K x) areaμ := by
    obtain ⟨κK, ΛK, hκK, hbK, _⟩ := h.2.2.1
    apply hW.mul_bdd h.1.aestronglyMeasurable (c := ΛK)
    filter_upwards [hbK] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hκK.le.trans hx.1)] using hx.2
  have hWJ : Integrable (fun x => W x * J x) areaμ :=
    hW.mul_bdd hJ.1 (by simpa only [Real.norm_eq_abs] using hJB)
  have hWJs (n : ℕ) : Integrable (fun x => W x * Js n x) areaμ :=
    hW.mul_bdd (hJs n).1.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hJsB n)
  have hlin (Q : ℝ → ℝ) (hQ : Integrable (fun x => W x * Q x) areaμ) :
      (∫ x, W x * (Q x - K x) ∂areaμ) =
        (∫ x, Q x * W x ∂areaμ) - ∫ x, W x * K x ∂areaμ := by
    simp_rw [mul_sub]
    rw [integral_sub hQ hWK]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  have hconv : Tendsto (fun n => ∫ x, W x * (Js n x - K x) ∂areaμ)
      atTop (𝓝 (∫ x, W x * (J x - K x) ∂areaμ)) := by
    simpa only [hlin J hWJ, hlin (Js _) (hWJs _)] using
      hJW.sub_const (∫ x, W x * K x ∂areaμ)
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hneg)).exists
  exact ⟨Js n, hJs n, hn⟩

private theorem exists_negative_on_segment {F : ℝ → ℝ} {v : ℝ}
    (hD : HasDerivAt F v 0) (hv : v < 0) (hzero : F 0 = 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, F t < 0 := by
  by_contra hn
  have hnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : F 0 ≤ F t := by
    rw [hzero]
    exact le_of_not_gt fun hlt => hn ⟨t, ht, hlt⟩
  have hLoc : IsLocalMinOn F (Icc (0 : ℝ) 1) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hnonneg t ht
  have hseg : segment ℝ (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [segment_eq_Icc zero_le_one]
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hp := hLoc.hasFDerivWithinAt_nonneg hD.hasFDerivAt.hasFDerivWithinAt hdir
  have hh : 0 ≤ v := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using hp
  exact (not_le_of_gt hv) hh

/-- Every cap strictly larger than an arbitrary cap carrying a zero-action
global minimum admits a negative original smooth unit-mass area competitor.
The complete curvature derivative, genuine feasible normalized segment and
full-action smooth recovery are used; no threshold identity or minimality
at the enlarged cap is assumed. -/
theorem IsRecoverableAreaCompetitor.exists_smooth_area_competitor_action_neg_of_zero_minimum
    {C C' : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (hCC' : C < C') :
    ∃ K' r' : ℝ → ℝ, IsSmoothAreaCompetitor C' K' r' ∧ meridionalAction K' r' < 0 := by
  have hC' : 1 ≤ C' := hC.le.trans hCC'.le
  obtain ⟨κ, t, a, b, η, hκ, _, _, hbox, _, _, _, _, _, _, _, hN,
      _, ha, hab, hb, hη, _, hfree⟩ :=
    h.exists_scale_balanced_free_curvature_interval hC hr hp hzero hmin
  let W := weakCurvatureAdjoint K r p z 0
  let Z := fun x => W x - t * (x - (1 / 2 : ℝ))
  obtain ⟨J, hJm, hJbox, hJ0, hJ1, hZDI, hZDneg⟩ :=
    Analysis.exists_moment_preserving_box_expansion h.1.aestronglyMeasurable hbox hN
      ha hab hb hη hfree (mul_lt_mul_of_pos_right hCC' hκ)
  have hratio : C' * κ / κ ≤ C' := by
    have he : C' * κ / κ = C' := by field_simp [hκ.ne']
    exact he.le
  have hJ : IsBoundedAreaCurvature C' J :=
    ⟨hJm, ⟨κ, C' * κ, hκ, hJbox, hratio⟩,
      hJ0.trans h.2.2.2.1, hJ1.trans h.2.2.2.2.1⟩
  have hKB : ∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C' * κ := by
    filter_upwards [hbox] with x hx
    exact ⟨hx.1, hx.2.trans (mul_le_mul_of_nonneg_right hCC'.le hκ.le)⟩
  have hKnew : IsBoundedAreaCurvature C' K :=
    ⟨h.1.aestronglyMeasurable, ⟨κ, C' * κ, hκ, hKB, hratio⟩,
      h.2.2.2.1, h.2.2.2.2.1⟩
  have hnew := h.of_curvature_cap hKnew
  have hKI : Integrable K areaμ := h.1.integrable (by norm_num)
  have hJI : Integrable J areaμ := hJ.memLp_curvature.integrable (by norm_num)
  let Δ := fun x => J x - K x
  have hDI : Integrable Δ areaμ := hJI.sub hKI
  have hxM : AEStronglyMeasurable (fun x : ℝ => x) areaμ :=
    continuous_id.aestronglyMeasurable
  have hxB : ∀ᵐ x ∂areaμ, ‖x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    exact hx.2.le
  have hJXI := hJI.bdd_mul hxM hxB
  have hKXI := hKI.bdd_mul hxM hxB
  have hDXI := hDI.bdd_mul hxM hxB
  have hJ0' : (∫ x, J x ∂areaμ) = ∫ x, K x ∂areaμ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hJ0
  have hJ1' : (∫ x, x * J x ∂areaμ) = ∫ x, x * K x ∂areaμ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hJ1
  have hM0 : (∫ x, Δ x ∂areaμ) = 0 := by
    change (∫ x, J x - K x ∂areaμ) = 0
    rw [integral_sub hJI hKI, hJ0', sub_self]
  have hM1 : (∫ x, x * Δ x ∂areaμ) = 0 := by
    calc
      _ = ∫ x, x * J x - x * K x ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_sub x (J x) (K x)
      _ = 0 := by rw [integral_sub hJXI hKXI, hJ1', sub_self]
  have hcM : AEStronglyMeasurable (fun x : ℝ => x - (1 / 2 : ℝ)) areaμ :=
    (continuous_id.sub continuous_const).aestronglyMeasurable
  have hcB : ∀ᵐ x ∂areaμ, ‖x - (1 / 2 : ℝ)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcI := hDI.bdd_mul hcM hcB
  have hc0 : (∫ x, (x - (1 / 2 : ℝ)) * Δ x ∂areaμ) = 0 := by
    calc
      _ = ∫ x, x * Δ x - (1 / 2 : ℝ) * Δ x ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => sub_mul x (1 / 2) (Δ x)
      _ = 0 := by
        rw [integral_sub hDXI (hDI.const_mul (1 / 2)), integral_const_mul, hM1, hM0]
        ring
  have hWEq : (∫ x, W x * Δ x ∂areaμ) = ∫ x, Z x * Δ x ∂areaμ := by
    calc
      _ = ∫ x, Z x * Δ x + t * ((x - (1 / 2 : ℝ)) * Δ x) ∂areaμ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [Z]
        ring
      _ = _ := by
        rw [integral_add hZDI (hcI.const_mul t), integral_const_mul, hc0, mul_zero, add_zero]
  have hWNeg : (∫ x, W x * (J x - K x) ∂areaμ) < 0 := hWEq.trans_lt hZDneg
  have hWI : Integrable W areaμ := h.weakCurvatureAdjoint_integrable hC.le 0
  obtain ⟨Q, hQ, hQNeg⟩ := exists_smooth_negative_pairing hnew hJ hWI hWNeg
  have hvar := hnew.curvature_variation_eq_integral_adjoint hC' Q hQ 0
  simp only [zero_mul, sub_zero] at hvar
  have hvarNeg : weakCurvatureSegmentVariation K Q r p z < 0 := by
    rw [hvar]
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hQNeg
  let F := fun τ => weakMeridionalAction (fun x => (1 - τ) * K x + τ * Q x) r p z
  have hF0 : F 0 = 0 := by
    simpa only [F, sub_zero, one_mul, zero_mul, add_zero] using hzero
  obtain ⟨τ, hτ, hτNeg⟩ := exists_negative_on_segment
    (weakMeridionalAction_curvature_segment_hasDerivAt hC' hnew Q hQ) hvarNeg hF0
  let Kτ := fun x => (1 - τ) * K x + τ * Q x
  let β := 1 / Real.sqrt (probeMass Kτ r)
  have hm : 0 < probeMass Kτ r := hnew.probeMass_curvature_segment_pos hC' Q hQ τ hτ
  have hβ : 0 < β := div_pos zero_lt_one (Real.sqrt_pos.mpr hm)
  have hRec := hnew.normalized_curvature_segment hC' Q hQ τ hτ
  have hNeg : weakMeridionalAction Kτ (fun x => β * r x)
      (fun x => β * p x) (fun x => β * z x) < 0 := by
    rw [weakMeridionalAction_const_mul]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hβ) hτNeg
  change IsRecoverableAreaCompetitor C' Kτ (fun x => β * r x)
    (fun x => β * p x) (fun x => β * z x) at hRec
  obtain ⟨_, _, Ks, rs, hS, _, _, _, _, hA⟩ := hRec.exists_action_recovery hC'
  obtain ⟨n, hn⟩ := (hA.eventually (gt_mem_nhds hNeg)).exists
  exact ⟨Ks n, rs n, hS n, hn⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile

namespace RicciFlowSharpEstimate.Geometry

open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature AreaProfile
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- An arbitrary actual zero-action global minimum at C₀ yields an original
smooth negative rotational metric/form witness with strict ratio room below
every D>C₀. All normalized curvature/probe, inverse maps, genuine jets and
same-metric dissipation bindings are retained. No identification with a
variational threshold or minimality at the larger cap is assumed. -/
theorem exists_smooth_geometric_negative_witness_above_zero_minimum
    {C₀ D : ℝ} {K₀ r₀ p₀ z₀ : ℝ → ℝ} (hC₀ : 1 < C₀)
    (h : IsRecoverableAreaCompetitor C₀ K₀ r₀ p₀ z₀)
    (hr : ContinuousOn r₀ (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p₀ (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K₀ r₀ p₀ z₀ = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C₀ K' r' p' z' →
      weakMeridionalAction K₀ r₀ p₀ z₀ ≤ weakMeridionalAction K' r' p' z')
    (hD : C₀ < D) :
    ∃ (C κ Λ : ℝ) (K r X : ℝ → ℝ) (P : RotationalProfile.PoleData)
      (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R),
      C₀ < C ∧ C < D ∧
      IsSmoothAreaCompetitor C K r ∧
      0 < κ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ) ∧
      Λ / κ ≤ C ∧ Λ / κ < D ∧
      (∫ x in (0 : ℝ)..1, K x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧
      probeMass K r = 1 ∧ meridionalAction K r < 0 ∧
      ContDiff ℝ ∞ X ∧
      heightCoordinate K 0 = -1 ∧ heightCoordinate K 1 = 1 ∧
      X (-1) = 0 ∧ X 1 = 1 ∧
      MapsTo (heightCoordinate K) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
      MapsTo X (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        X (heightCoordinate K x) = x ∧
        P.a (heightCoordinate K x) = 1 / K x ∧
        R (heightCoordinate K x) = r x ∧
        RotationalProfile.warp P.a (heightCoordinate K x) = warp K x) ∧
      (∀ v ∈ Icc (-1 : ℝ) 1,
        heightCoordinate K (X v) = v ∧ deriv X v * K (X v) = 1) ∧
      R = r ∘ X ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        deriv P.a (heightCoordinate K x) = -deriv K x / K x ^ 3 ∧
        deriv R (heightCoordinate K x) = deriv r x / K x ∧
        deriv (deriv R) (heightCoordinate K x) =
          deriv (deriv r) x / K x ^ 2 - deriv r x * deriv K x / K x ^ 3) ∧
      (∀ p : RotationalSphere,
        metricScalarAt P.metric p / 2 = K (X (sphereHeight p))) ∧
      oneFormDissipation P.metric (P.meridionalOneForm R hR) =
        2 * Real.pi * meridionalAction K r ∧
      IsRepresentedRotationalMetric P.metric ∧
      (∀ p : RotationalSphere,
        κ ≤ metricScalarAt P.metric p / 2 ∧ metricScalarAt P.metric p / 2 ≤ Λ) ∧
      P.meridionalOneForm R hR ≠ 0 ∧
      oneFormDissipation P.metric (P.meridionalOneForm R hR) < 0 := by
  obtain ⟨C, hCC, hCD⟩ := exists_between hD
  obtain ⟨K, r, hcomp, hnegArea⟩ :=
    h.exists_smooth_area_competitor_action_neg_of_zero_minimum hC₀ hr hp hzero hmin hCC
  have hdata := hcomp
  rcases hdata with ⟨hK, hr', ⟨κ, Λ, hκ, hbox, hratio⟩, hzero', hone, hmass⟩
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < K x :=
    hκ.trans_le (hbox x hx).1
  obtain ⟨X, P, R, hR, hX, hV0, hV1, hX0, hX1, hVmap, hXmap,
      hforward, hbackward, hcompR, hjets, hcurv, haction⟩ :=
    exists_smooth_geometric_realization K r hK hr' hpos hzero' hone
  have hneg : oneFormDissipation P.metric (P.meridionalOneForm R hR) < 0 := by
    rw [haction]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hnegArea
  have hnz : P.meridionalOneForm R hR ≠ 0 := by
    intro hz
    have hh := hneg
    rw [hz, oneFormDissipation_zero] at hh
    exact (lt_irrefl 0) hh
  have hgeo (p : RotationalSphere) :
      κ ≤ metricScalarAt P.metric p / 2 ∧ metricScalarAt P.metric p / 2 ≤ Λ := by
    rw [hcurv p]
    exact hbox _ (hXmap (sphereHeight_mem_Icc p))
  exact ⟨C, κ, Λ, K, r, X, P, R, hR, hCC, hCD, hcomp, hκ, hbox, hratio,
    hratio.trans_lt hCD, hzero', hone, hmass, hnegArea, hX, hV0, hV1, hX0, hX1,
    hVmap, hXmap, hforward, hbackward, hcompR, hjets, hcurv, haction,
    P.isRepresentedRotationalMetric, hgeo, hnz, hneg⟩

end RicciFlowSharpEstimate.Geometry
