/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjoint
import RicciFlowSharpEstimate.Analysis.BoundedWeakPairing
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers

/-!
# The actual minimum's curvature inequality for measurable comparisons

Same-box exact-moment recovery extends the full integrable-adjoint inequality
to every bounded measurable admissible curvature. Pairing convergence follows
from strong L2 convergence and the common essential bound; no false continuity
of the quadratic curvature potential is used.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual joint minimum satisfies the complete mass-corrected adjoint
inequality for every bounded measurable curvature with both physical moments
and its own original ratio box. No symmetry or smoothness is imposed on the
comparison curvature. -/
theorem IsRecoverableAreaCompetitor.bounded_curvature_adjoint_inequality_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (J : ℝ → ℝ) (hJ : IsBoundedAreaCurvature C J) :
    0 ≤ ∫ s in (0 : ℝ)..1,
      weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z) s * (J s - K s) := by
  let W := weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z)
  have hW : Integrable W areaμ := h.weakCurvatureAdjoint_integrable hC _
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
  have hpairI : Tendsto (fun n => ∫ s in (0 : ℝ)..1, W s * (Js n s - K s))
      atTop (𝓝 (∫ s in (0 : ℝ)..1, W s * (J s - K s))) := by
    have ht := hJW.sub_const (∫ x, W x * K x ∂areaμ)
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      hlin J hWJ, hlin (Js _) (hWJs _)] using ht
  exact ge_of_tendsto' hpairI (fun n =>
    h.curvature_adjoint_inequality_of_minimum hC hmin (Js n) (hJs n))

/-- A cap alone produces the actual physically nonzero joint weak minimum,
its complete weak probe equation, and an integrable curvature adjoint with
its inequality against every bounded measurable admissible comparison.
This is a necessary-condition theorem, not a threshold selection theorem. -/
theorem exists_recoverable_area_minimizer_with_bounded_curvature_adjoint
    (C : ℝ) (hC : 1 ≤ C) :
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
      (∀ J : ℝ → ℝ, IsBoundedAreaCurvature C J →
        0 ≤ ∫ s in (0 : ℝ)..1,
          weakCurvatureAdjoint K r p z (smoothAreaInfimum C) s * (J s - K s)) := by
  obtain ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe, hW, _⟩ :=
    exists_recoverable_area_minimizer_with_curvature_adjoint C hC
  refine ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe, hW, ?_⟩
  intro J hJ
  simpa only [hEq] using h.bounded_curvature_adjoint_inequality_of_minimum hC hmin J hJ

end RicciFlowSharpEstimate.Geometry.AreaProfile
