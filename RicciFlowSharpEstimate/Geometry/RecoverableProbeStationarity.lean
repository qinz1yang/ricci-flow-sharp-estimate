/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableProbeVariation
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization
import RicciFlowSharpEstimate.Geometry.AreaJointMinimum

/-!
# Weak probe stationarity of the actual recoverable joint minimum

Normalized smooth probe perturbations are proved feasible in the same weak
class. The complete-action and mass polynomial identities give the genuine
weak equation, with the actual action as eigenvalue. No smoothness of the
limiting curvature, artificial pole condition or zero eigenvalue is assumed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- An actual minimum on the recoverable class satisfies the complete weak
probe equation for every smooth direction, including nonzero endpoint
values and derivatives. The eigenvalue is its actual unit-mass action. -/
theorem IsRecoverableAreaCompetitor.weak_probe_equation_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (s : ℝ → ℝ) (hs : ContDiff ℝ ∞ s) :
    weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
      weakMeridionalAction K r p z * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGeo := h.geometry_bounds hC
  have hgraph := h.2.1
  have hgraphS := Analysis.hasParabolicWeakDerivatives_of_contDiff (hs.of_le (by simp))
  have hf : AEStronglyMeasurable (warp K) areaμ :=
    ((hGeo.1.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hb : AEStronglyMeasurable (warpSlope K) areaμ :=
    ((hGeo.2.1.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hGeo.2.2.2.2] with x hx
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1, hx.2⟩
  have hfbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp K x ∧ warp K x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := hGeo.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    refine ⟨?_, by simpa only [mul_assoc] using hg.2.1⟩
    exact (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hg.1
  have hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hGeo.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hDA : HasDerivAt
      (fun t => weakMeridionalAction K (fun x => r x + t * s x)
        (fun x => p x + t * deriv s x) (fun x => z x + t * deriv (deriv s) x))
      (2 * weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s))) 0 := by
    simpa only [mul_zero, zero_mul, add_zero] using weakMeridionalAction_hasDerivAt
      K r p z s (deriv s) (deriv (deriv s)) (2 * C) hgraph hgraphS
      (by positivity) h.1.aestronglyMeasurable hf hb hKbox hfbox hbbox 0
  have hDM : HasDerivAt (fun t => probeMass K (fun x => r x + t * s x))
      (2 * ∫ x in (0 : ℝ)..1, warp K x * s x * r x) 0 := by
    simpa only [mul_zero, zero_mul, add_zero] using probeMass_hasDerivAt_of_warp_bounds
      K r s (2 * C) hgraph.memLp hgraphS.memLp
      (by positivity) hf hfbox 0
  have hunit : probeMass K r = 1 := h.2.2.2.2.2.1
  have hm0 : 0 < probeMass K (fun x => r x + (0 : ℝ) * s x) := by
    simpa only [zero_mul, add_zero, hunit] using (zero_lt_one : (0 : ℝ) < 1)
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < probeMass K (fun x => r x + t * s x) :=
    hDM.continuousAt.eventually (lt_mem_nhds hm0)
  let F : ℝ → ℝ := fun t =>
    weakMeridionalAction K (fun x => r x + t * s x)
      (fun x => p x + t * deriv s x) (fun x => z x + t * deriv (deriv s) x) -
      weakMeridionalAction K r p z * probeMass K (fun x => r x + t * s x)
  have hDF := hDA.sub (hDM.const_mul (weakMeridionalAction K r p z))
  have hLocal : IsLocalMin F 0 := by
    filter_upwards [hpos] with t ht
    have hfeas := h.normalized_probe_add_mul hC s hs t ht
    have hc := hmin K _ _ _ hfeas
    let m : ℝ := probeMass K (fun x => r x + t * s x)
    let c : ℝ := 1 / Real.sqrt m
    change weakMeridionalAction K r p z ≤
      weakMeridionalAction K (fun x => c * (r x + t * s x))
        (fun x => c * (p x + t * deriv s x))
        (fun x => c * (z x + t * deriv (deriv s) x)) at hc
    rw [weakMeridionalAction_const_mul] at hc
    have hcm : c ^ 2 * m = 1 := by
      dsimp only [c]
      rw [one_div_pow, Real.sq_sqrt ht.le]
      exact one_div_mul_cancel ht.ne'
    have hmul := mul_le_mul_of_nonneg_right hc ht.le
    have hcancel :
        (c ^ 2 * weakMeridionalAction K (fun x => r x + t * s x)
          (fun x => p x + t * deriv s x) (fun x => z x + t * deriv (deriv s) x)) * m =
        weakMeridionalAction K (fun x => r x + t * s x)
          (fun x => p x + t * deriv s x) (fun x => z x + t * deriv (deriv s) x) := by
      calc
        _ = (c ^ 2 * m) * weakMeridionalAction K (fun x => r x + t * s x)
            (fun x => p x + t * deriv s x) (fun x => z x + t * deriv (deriv s) x) := by ring
        _ = _ := by rw [hcm, one_mul]
    change weakMeridionalAction K r p z * m ≤ _ at hmul
    rw [hcancel] at hmul
    simpa only [F, zero_mul, add_zero, hunit, mul_one, sub_self] using
      (sub_nonneg.mpr hmul)
  have hzero := hLocal.hasDerivAt_eq_zero hDF
  linarith only [hzero]

/-- Every cap at least one produces a physically nonzero joint minimum
satisfying the complete weak probe equation in every smooth direction.
Its eigenvalue is the actual smooth-class infimum, not an assumed zero. -/
theorem exists_recoverable_area_minimizer_weak_probe_equation (C : ℝ) (hC : 1 ≤ C) :
    ∃ K r p z : ℝ → ℝ,
      IsRecoverableAreaCompetitor C K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      weakMeridionalAction K r p z = smoothAreaInfimum C ∧
      (∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') ∧
      (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
        weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
          smoothAreaInfimum C * (∫ x in (0 : ℝ)..1, warp K x * s x * r x)) := by
  obtain ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin⟩ := exists_recoverable_area_minimizer C hC
  refine ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, ?_⟩
  intro s hs
  simpa only [hEq] using h.weak_probe_equation_of_minimum hC hmin s hs

end RicciFlowSharpEstimate.Geometry.AreaProfile
