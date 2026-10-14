/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjoint

/-!
# The global scaling identity for the complete curvature adjoint

The own-curvature Green representation and weighted Fubini give the cubic
Euler identity for the actual adjoint, including its mass correction. This is
an integral identity; rescaling curvature alone is not asserted admissible.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem own_green_primitives (K : ℝ → ℝ)
    (hKi : Integrable K areaμ)
    (h0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (h1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    2 * (∫ s, Analysis.unitDirichletKernel x s * K s ∂areaμ) = warp K x ∧
    2 * (∫ s, Analysis.unitDirichletSlopeKernel x s * K s ∂areaμ) = warpSlope K x := by
  have hK : IntervalIntegrable K volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hKi
  have hxK : IntervalIntegrable (fun s : ℝ => s * K s) volume 0 1 :=
    hK.continuousOn_mul continuous_id.continuousOn
  have hm : (∫ s in (0 : ℝ)..1, (1 - s) * K s) = 1 := by
    calc
      _ = ∫ s in (0 : ℝ)..1, K s - s * K s := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = 1 := by rw [intervalIntegral.integral_sub hK hxK, h0, h1]; norm_num
  have hG := Analysis.integral_unitDirichletKernel K hKi x hx
  have hB := Analysis.integral_unitDirichletSlopeKernel K hKi x hx
  rw [hm] at hG hB
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    at hG hB
  constructor
  · rw [hG]
    unfold warp
    ring
  · rw [hB]
    unfold warpSlope
    ring

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

private theorem slope_bound_ae :
    ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ,
      |Analysis.unitDirichletSlopeKernel v.1 v.2| ≤ |(1 : ℝ)| := by
  have hs : ∀ᵐ v : ℝ × ℝ ∂(areaμ).prod areaμ, v.2 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hs] with v hy
  simpa only [abs_one] using
    Analysis.abs_unitDirichletSlopeKernel_le_one v.1 v.2 ⟨hy.1.le, hy.2.le⟩

/-- Pairing the actual curvature with its complete adjoint gives the cubic
action homogeneity minus the degree-one mass correction. All integrability
is derived from the genuine recoverable graph and original positive box.
No physical curvature-scaling path is assumed feasible. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_scale_identity
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (lam : ℝ) :
    Integrable (fun x => weakCurvatureAdjoint K r p z lam x * K x) areaμ ∧
    (∫ x, weakCurvatureAdjoint K r p z lam x * K x ∂areaμ) =
      3 * weakMeridionalAction K r p z - lam * probeMass K r := by
  obtain ⟨hA, hWA, hB, hD⟩ := h.curvature_coefficients_integrable hC
  let S : ℝ → ℝ := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let D := weakCurvatureCoefficient K r p z
  have hwm : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hwb : ∀ᵐ x ∂areaμ, ‖x * (1 - x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  have hSm : AEStronglyMeasurable S areaμ :=
    hA.sub ((h.2.1.memLp.aestronglyMeasurable.pow 2).const_mul lam)
  have hSW : Integrable (fun x => x * (1 - x) * S x) areaμ := by
    apply (hWA.sub ((h.2.1.integrable_sq.bdd_mul hwm hwb).const_mul lam)).congr
    filter_upwards [] with x
    dsimp only [S, Pi.sub_apply]
    ring
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKb : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [(h.geometry_bounds hC).2.2.2.2] with x hx
    have hk : 0 ≤ K x := (by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1
    simpa only [abs_of_nonneg hk] using hx.2
  have hG := Analysis.integral_kernel_pairing_of_weighted_integrable
    Analysis.measurable_unitDirichletKernel.aestronglyMeasurable hSm hSW
    green_bound_ae h.1.aestronglyMeasurable hKb
  have hH := Analysis.integral_kernel_pairing_of_weighted_integrable
    Analysis.measurable_unitDirichletSlopeKernel.aestronglyMeasurable hB.aestronglyMeasurable
    (by simpa only [one_mul] using hB : Integrable (fun x => (1 : ℝ) * B x) areaμ)
    slope_bound_ae h.1.aestronglyMeasurable hKb
  have hDK : Integrable (fun x => D x * K x) areaμ :=
    hD.mul_bdd h.1.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hKb)
  have hWKi : Integrable (fun x => weakCurvatureAdjoint K r p z lam x * K x) areaμ :=
    (h.weakCurvatureAdjoint_integrable hC lam).mul_bdd h.1.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hKb)
  have hHt : Integrable (fun x =>
      (∫ s, Analysis.unitDirichletSlopeKernel s x * B s ∂areaμ) * K x) areaμ := hH.2.1
  have hHs : Integrable (fun x =>
      B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * K s ∂areaμ)) areaμ := hH.1
  have hRsum : Integrable (fun x => D x * K x +
      2 * ((∫ s, Analysis.unitDirichletKernel s x * S s ∂areaμ) * K x)) areaμ :=
    hDK.add (hG.2.1.const_mul 2)
  have hLsum : Integrable (fun x => D x * K x +
      2 * (S x * (∫ s, Analysis.unitDirichletKernel x s * K s ∂areaμ))) areaμ :=
    hDK.add (hG.1.const_mul 2)
  refine ⟨hWKi, ?_⟩
  have hsplit : (∫ x, weakCurvatureAdjoint K r p z lam x * K x ∂areaμ) =
      (∫ x, D x * K x ∂areaμ) +
      2 * (∫ x, S x * (∫ s, Analysis.unitDirichletKernel x s * K s ∂areaμ) ∂areaμ) +
      2 * (∫ x, B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * K s ∂areaμ) ∂areaμ) := by
    calc
      _ = ∫ x, (D x * K x +
          2 * ((∫ s, Analysis.unitDirichletKernel s x * S s ∂areaμ) * K x)) +
          2 * ((∫ s, Analysis.unitDirichletSlopeKernel s x * B s ∂areaμ) * K x) ∂areaμ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [weakCurvatureAdjoint, S, B, D]
        ring
      _ = _ := by
        rw [integral_add hRsum (hHt.const_mul 2),
          integral_add hDK (hG.2.1.const_mul 2), integral_const_mul,
          integral_const_mul, ← hG.2.2, ← hH.2.2]
  rw [hsplit]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add hDK (hG.1.const_mul 2),
    ← integral_add hLsum (hHs.const_mul 2)]
  have heq : (fun x => (D x * K x +
      2 * (S x * (∫ s, Analysis.unitDirichletKernel x s * K s ∂areaμ))) +
      2 * (B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * K s ∂areaμ))) =ᵐ[areaμ]
      (fun x => 3 * meridionalActionDensity (warp K x) (warpSlope K x)
        (K x) (r x) (p x) (z x) - lam * (warp K x * r x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨hf, hb⟩ := own_green_primitives K (h.1.integrable (by norm_num))
      h.2.2.2.1 h.2.2.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    rw [show 2 * (S x * (∫ s, Analysis.unitDirichletKernel x s * K s ∂areaμ)) =
        S x * warp K x by rw [← hf]; ring,
      show 2 * (B x * (∫ s, Analysis.unitDirichletSlopeKernel x s * K s ∂areaμ)) =
        B x * warpSlope K x by rw [← hb]; ring]
    dsimp only [D, B, S, weakCurvatureCoefficient, weakCurvatureSlopeCoefficient,
      weakCurvatureWarpCoefficient, weakMeridionalOperator, meridionalActionDensity]
    ring
  rw [integral_congr_ae heq]
  obtain ⟨hAi, hMi, _⟩ := h.exists_action_recovery hC
  rw [integral_sub (hAi.const_mul 3) (hMi.const_mul lam),
    integral_const_mul, integral_const_mul]
  simp only [weakMeridionalAction, probeMass,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end RicciFlowSharpEstimate.Geometry.AreaProfile
