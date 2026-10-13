/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeightedKernelPairing
import RicciFlowSharpEstimate.Geometry.AreaGreenPrimitives
import RicciFlowSharpEstimate.Geometry.WeakCurvatureCoefficients
import RicciFlowSharpEstimate.Geometry.RecoverableCurvatureOptimality

/-!
# An integrable curvature adjoint for the actual weak minimum

The Dirichlet kernel retains the polar weight of the warp coefficient.
Fubini therefore represents the complete mass-corrected curvature variation
by a genuine integrable density, without assuming unweighted integrability
of the warp coefficient. The actual minimum satisfies its pairing inequality.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The complete curvature adjoint with the physical mass correction.
The parameter is the mass multiplier, not an extracted moment multiplier. -/
def weakCurvatureAdjoint (K r p z : ℝ → ℝ) (lam : ℝ) (s : ℝ) : ℝ :=
  weakCurvatureCoefficient K r p z s +
    2 * (∫ x, Analysis.unitDirichletKernel x s *
      (weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2) ∂areaμ) +
    2 * (∫ x, Analysis.unitDirichletSlopeKernel x s *
      weakCurvatureSlopeCoefficient K r p z x ∂areaμ)

private theorem green_bound_ae :
    ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ,
      |Analysis.unitDirichletKernel v.1 v.2| ≤ |v.1 * (1 - v.1)| := by
  have hf : ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ, v.1 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  have hs : ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ, v.2 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hf, hs] with v hx hy
  exact (Analysis.abs_unitDirichletKernel_le v.1 v.2
    ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩).trans (le_abs_self _)

private theorem green_slope_bound_ae :
    ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ,
      |Analysis.unitDirichletSlopeKernel v.1 v.2| ≤ |(1 : ℝ)| := by
  have hs : ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ, v.2 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hs] with v hy
  simpa only [abs_one] using
    Analysis.abs_unitDirichletSlopeKernel_le_one v.1 v.2 ⟨hy.1.le, hy.2.le⟩

private theorem lagrange_coefficients_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (lam : ℝ) :
    AEStronglyMeasurable
      (fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2) areaμ ∧
    Integrable (fun x => x * (1 - x) *
      (weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2)) areaμ ∧
    Integrable (weakCurvatureSlopeCoefficient K r p z) areaμ ∧
    Integrable (weakCurvatureCoefficient K r p z) areaμ := by
  obtain ⟨hA, hWA, hB, hD⟩ := h.curvature_coefficients_integrable hC
  have hwm : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hwb : ∀ᵐ x ∂areaμ, ‖x * (1 - x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  have hWR := h.2.1.integrable_sq.bdd_mul hwm hwb
  refine ⟨hA.sub ((h.2.1.memLp.aestronglyMeasurable.pow 2).const_mul lam), ?_, hB, hD⟩
  apply (hWA.sub (hWR.const_mul lam)).congr
  filter_upwards [] with x
  change x * (1 - x) * weakCurvatureWarpCoefficient K r p z x -
      lam * (x * (1 - x) * r x ^ 2) = _
  ring

/-- The actual mass-corrected curvature adjoint is integrable for every
recoverable weak competitor, despite the potentially singular unweighted
warp coefficient. -/
theorem IsRecoverableAreaCompetitor.weakCurvatureAdjoint_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (lam : ℝ) :
    Integrable (weakCurvatureAdjoint K r p z lam) areaμ := by
  obtain ⟨hA, hWA, hB, hD⟩ := lagrange_coefficients_integrable hC h lam
  have hG := Analysis.integrable_kernel_adjoint_of_weighted_integrable
    Analysis.measurable_unitDirichletKernel.aestronglyMeasurable hA hWA green_bound_ae
  have hH := Analysis.integrable_kernel_adjoint_of_weighted_integrable
    Analysis.measurable_unitDirichletSlopeKernel.aestronglyMeasurable hB.aestronglyMeasurable
    (by simpa only [one_mul] using hB :
      Integrable (fun x => (1 : ℝ) * weakCurvatureSlopeCoefficient K r p z x) areaμ)
    green_slope_bound_ae
  exact (hD.add (hG.const_mul 2)).add (hH.const_mul 2)

private theorem comparison_curvature_bound
    {C : ℝ} {K r p z J : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (hJ : IsSmoothAreaCurvature C J) :
    ∀ᵐ x ∂areaμ, |J x - K x| ≤ 4 * C := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  filter_upwards [(h.geometry_bounds hC).2.2.2.2,
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have hj := hJ.common_bounds x ⟨hxI.1.le, hxI.2.le⟩
  have hK0 : 0 ≤ K x := (by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1
  have hJ0 : 0 ≤ J x := (by positivity : (0 : ℝ) ≤ 2 / C).trans hj.1
  calc
    |J x - K x| ≤ |J x| + |K x| := abs_sub _ _
    _ = J x + K x := by rw [abs_of_nonneg hJ0, abs_of_nonneg hK0]
    _ ≤ 4 * C := by linarith [hj.2, hx.2]

private theorem comparison_mass_integrable
    {C : ℝ} {K r p z J : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (hJ : IsSmoothAreaCurvature C J) :
    Integrable (fun x => (warp J x - warp K x) * r x ^ 2) areaμ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hfJ : AEStronglyMeasurable (warp J) areaμ :=
    (warp_continuous J hJ.1.continuous).aestronglyMeasurable
  have hfJbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp J x ∧ warp J x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := hJ.geometry_bounds x ⟨hx.1.le, hx.2.le⟩
    refine ⟨?_, by simpa only [mul_assoc] using hg.2.1⟩
    exact (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hg.1
  have hMJ := integrable_probeMassDensity_of_warp_bounds J r (2 * C)
    h.2.1.memLp (by positivity) hfJ hfJbox
  apply (hMJ.sub (h.exists_action_recovery hC).2.1).congr
  filter_upwards [] with x
  change warp J x * r x ^ 2 - warp K x * r x ^ 2 = _
  ring

/-- The actual complete curvature variation, including the physical mass
correction, is the pairing with the integrable Green adjoint. -/
theorem IsRecoverableAreaCompetitor.curvature_variation_eq_integral_adjoint
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (J : ℝ → ℝ)
    (hJ : IsSmoothAreaCurvature C J) (lam : ℝ) :
    weakCurvatureSegmentVariation K J r p z -
      lam * (∫ x in (0 : ℝ)..1, (warp J x - warp K x) * r x ^ 2) =
      ∫ s in (0 : ℝ)..1, weakCurvatureAdjoint K r p z lam s * (J s - K s) := by
  obtain ⟨hA, hWA, hB, hD⟩ := lagrange_coefficients_integrable hC h lam
  let S : ℝ → ℝ := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B : ℝ → ℝ := weakCurvatureSlopeCoefficient K r p z
  let D : ℝ → ℝ := weakCurvatureCoefficient K r p z
  let ξ : ℝ → ℝ := fun s => J s - K s
  have hξ : AEStronglyMeasurable ξ areaμ :=
    hJ.memLp_curvature.aestronglyMeasurable.sub h.1.aestronglyMeasurable
  have hξb := comparison_curvature_bound hC h hJ
  have hξnorm : ∀ᵐ s ∂areaμ, ‖ξ s‖ ≤ 4 * C := by
    simpa only [Real.norm_eq_abs] using hξb
  have hG := Analysis.integral_kernel_pairing_of_weighted_integrable
    Analysis.measurable_unitDirichletKernel.aestronglyMeasurable hA hWA green_bound_ae hξ hξb
  have hH := Analysis.integral_kernel_pairing_of_weighted_integrable
    Analysis.measurable_unitDirichletSlopeKernel.aestronglyMeasurable hB.aestronglyMeasurable
    (by simpa only [one_mul] using hB : Integrable (fun x => (1 : ℝ) * B x) areaμ)
    green_slope_bound_ae hξ hξb
  have hDξ : Integrable (fun s => D s * ξ s) areaμ := hD.mul_bdd hξ hξnorm
  have hKi := h.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hJi := hJ.memLp_curvature.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hzero : (∫ s in (0 : ℝ)..1, J s) = ∫ s in (0 : ℝ)..1, K s := by
    rw [hJ.2.2.1, h.2.2.2.1]
  have hfirst : (∫ s in (0 : ℝ)..1, s * J s) = ∫ s in (0 : ℝ)..1, s * K s := by
    rw [hJ.2.2.2, h.2.2.2.2.1]
  have hwarp (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      warp J x - warp K x =
        2 * ∫ s, Analysis.unitDirichletKernel x s * ξ s ∂areaμ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] using
      warp_sub_eq_integral_unitDirichletKernel J K hJi hKi hzero hfirst x ⟨hx.1.le, hx.2.le⟩
  have hslope (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      warpSlope J x - warpSlope K x =
        2 * ∫ s, Analysis.unitDirichletSlopeKernel x s * ξ s ∂areaμ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] using
      warpSlope_sub_eq_integral_unitDirichletSlopeKernel J K hJi hKi hzero hfirst x
        ⟨hx.1.le, hx.2.le⟩
  have halgebra (x : ℝ) : weakCurvatureSegmentDensity K J r p z x -
      lam * ((warp J x - warp K x) * r x ^ 2) =
      S x * (warp J x - warp K x) + B x * (warpSlope J x - warpSlope K x) + D x * ξ x := by
    dsimp only [S, B, D, ξ, weakCurvatureSegmentDensity, weakCurvatureWarpCoefficient,
      weakCurvatureSlopeCoefficient, weakCurvatureCoefficient]
    ring
  have hV := weakCurvatureSegmentDensity_integrable hC h hJ
  have hM := comparison_mass_integrable hC h hJ
  simp only [weakCurvatureSegmentVariation, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  rw [← integral_const_mul lam, ← integral_sub hV (hM.const_mul lam)]
  calc
    _ = ∫ x, 2 * (S x * (∫ s, Analysis.unitDirichletKernel x s * ξ s ∂areaμ)) +
        2 * (B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * ξ s ∂areaμ)) +
        D x * ξ x ∂areaμ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [halgebra, hwarp x hx, hslope x hx]
      ring
    _ = 2 * (∫ x, S x * (∫ s, Analysis.unitDirichletKernel x s * ξ s ∂areaμ) ∂areaμ) +
        2 * (∫ x, B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * ξ s ∂areaμ) ∂areaμ) +
        ∫ x, D x * ξ x ∂areaμ := by
      have hsum : Integrable (fun x =>
          2 * (S x * (∫ s, Analysis.unitDirichletKernel x s * ξ s ∂areaμ)) +
          2 * (B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * ξ s ∂areaμ))) areaμ := by
        apply ((hG.1.const_mul 2).add (hH.1.const_mul 2)).congr
        exact Eventually.of_forall fun _ => rfl
      rw [integral_add hsum hDξ,
        integral_add (hG.1.const_mul 2) (hH.1.const_mul 2)]
      simp only [integral_const_mul, S, B]
    _ = ∫ s, 2 * ((∫ x, Analysis.unitDirichletKernel x s * S x ∂areaμ) * ξ s) +
        2 * ((∫ x, Analysis.unitDirichletSlopeKernel x s * B x ∂areaμ) * ξ s) +
        D s * ξ s ∂areaμ := by
      have hsum : Integrable (fun s =>
          2 * ((∫ x, Analysis.unitDirichletKernel x s * S x ∂areaμ) * ξ s) +
          2 * ((∫ x, Analysis.unitDirichletSlopeKernel x s * B x ∂areaμ) * ξ s)) areaμ := by
        apply ((hG.2.1.const_mul 2).add (hH.2.1.const_mul 2)).congr
        exact Eventually.of_forall fun _ => rfl
      rw [hG.2.2, hH.2.2, integral_add hsum hDξ,
        integral_add (hG.2.1.const_mul 2) (hH.2.1.const_mul 2)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      dsimp only [weakCurvatureAdjoint, S, B, D, ξ]
      ring

/-- Actual recoverable minimality gives the pairing inequality for the
complete integrable curvature adjoint and every admissible smooth comparison. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_inequality_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (J : ℝ → ℝ) (hJ : IsSmoothAreaCurvature C J) :
    0 ≤ ∫ s in (0 : ℝ)..1,
      weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z) s * (J s - K s) := by
  rw [← h.curvature_variation_eq_integral_adjoint hC J hJ]
  exact h.curvature_segment_inequality_of_minimum hC hmin J hJ

/-- A cap alone produces the actual joint weak minimum, its probe equation,
and its integrable curvature adjoint inequality. No moment multiplier,
structural family or threshold selection is assumed or concluded. -/
theorem exists_recoverable_area_minimizer_with_curvature_adjoint (C : ℝ) (hC : 1 ≤ C) :
    ∃ K r p z : ℝ → ℝ,
      IsRecoverableAreaCompetitor C K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      weakMeridionalAction K r p z = smoothAreaInfimum C ∧
      (∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') ∧
      (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
        weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
          smoothAreaInfimum C * (∫ x in (0 : ℝ)..1, warp K x * s x * r x)) ∧
      Integrable (weakCurvatureAdjoint K r p z (smoothAreaInfimum C)) areaμ ∧
      (∀ J : ℝ → ℝ, IsSmoothAreaCurvature C J →
        0 ≤ ∫ s in (0 : ℝ)..1,
          weakCurvatureAdjoint K r p z (smoothAreaInfimum C) s * (J s - K s)) := by
  obtain ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe, _⟩ :=
    exists_recoverable_area_minimizer_weak_conditions C hC
  refine ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe,
    h.weakCurvatureAdjoint_integrable hC _, ?_⟩
  intro J hJ
  simpa only [hEq] using h.curvature_adjoint_inequality_of_minimum hC hmin J hJ

end RicciFlowSharpEstimate.Geometry.AreaProfile
