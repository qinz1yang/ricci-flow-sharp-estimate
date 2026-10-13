/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableProbeMultiplication
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization
import RicciFlowSharpEstimate.Geometry.AreaJointMinimum

/-!
# Multiplicative variations of the actual recoverable minimum

Multiplication by a smooth factor gives a genuine feasible weak direction even
when the limiting probe is not smooth. The full action and varying mass yield
the corresponding weak equation; the eigenvalue is the actual unit-mass action.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Every smooth multiplier of the probe is an admissible weak direction at
an actual recoverable minimum. The product jets remain tied to the same probe. -/
theorem IsRecoverableAreaCompetitor.weak_probe_mul_equation_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    weakMeridionalPairing K r p z
      (fun x => r x * u x)
      (fun x => p x * u x + r x * deriv u x)
      (fun x => z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x) =
      weakMeridionalAction K r p z * (∫ x in (0 : ℝ)..1, warp K x * (r x * u x) * r x) := by
  let s : ℝ → ℝ := fun x => r x * u x
  let q : ℝ → ℝ := fun x => p x * u x + r x * deriv u x
  let v : ℝ → ℝ := fun x => z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGeo := h.geometry_bounds hC
  have hgraph := h.2.1
  have hgraphS := hgraph.mul_contDiff u hu
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
        (fun x => p x + t * q x) (fun x => z x + t * v x))
      (2 * weakMeridionalPairing K r p z s q v) 0 := by
    simpa only [mul_zero, zero_mul, add_zero] using weakMeridionalAction_hasDerivAt
      K r p z s q v (2 * C) hgraph hgraphS
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
      (fun x => p x + t * q x) (fun x => z x + t * v x) -
      weakMeridionalAction K r p z * probeMass K (fun x => r x + t * s x)
  have hDF := hDA.sub (hDM.const_mul (weakMeridionalAction K r p z))
  have hLocal : IsLocalMin F 0 := by
    filter_upwards [hpos] with t ht
    have hd : deriv (fun x => 1 + t * u x) = fun x => t * deriv u x := by
      funext x
      exact ((hu.differentiable (by simp) x).hasDerivAt.const_mul t |>.const_add 1).deriv
    have hdd : deriv (deriv (fun x => 1 + t * u x)) =
        fun x => t * deriv (deriv u) x := by
      rw [hd]
      exact deriv_const_mul_field' t
    have hrEq : (fun x => r x * (1 + t * u x)) = fun x => r x + t * s x := by
      funext x
      dsimp only [s]
      ring
    have hpEq : (fun x => p x * (1 + t * u x) + r x * (t * deriv u x)) =
        fun x => p x + t * q x := by
      funext x
      dsimp only [q]
      ring
    have hzEq : (fun x => z x * (1 + t * u x) +
        2 * p x * (t * deriv u x) + r x * (t * deriv (deriv u) x)) =
        fun x => z x + t * v x := by
      funext x
      dsimp only [v]
      ring
    have ht' : 0 < probeMass K (fun x => r x * (1 + t * u x)) := by
      rw [hrEq]
      exact ht
    have hfeas := h.normalized_probe_mul hC (fun x => 1 + t * u x)
      (contDiff_const.add (contDiff_const.mul hu)) ht'
    rw [hdd] at hfeas
    simp only [hd, hrEq] at hfeas
    change IsRecoverableAreaCompetitor C K _
      (fun x => (1 / Real.sqrt (probeMass K (fun y => r y + t * s y))) *
        ((fun y => p y * (1 + t * u y) + r y * (t * deriv u y)) x))
      (fun x => (1 / Real.sqrt (probeMass K (fun y => r y + t * s y))) *
        ((fun y => z y * (1 + t * u y) + 2 * p y * (t * deriv u y) +
          r y * (t * deriv (deriv u) y)) x)) at hfeas
    rw [hpEq, hzEq] at hfeas
    have hc := hmin K _ _ _ hfeas
    let m : ℝ := probeMass K (fun x => r x + t * s x)
    let c : ℝ := 1 / Real.sqrt m
    change weakMeridionalAction K r p z ≤
      weakMeridionalAction K (fun x => c * (r x + t * s x))
        (fun x => c * (p x + t * q x))
        (fun x => c * (z x + t * v x)) at hc
    rw [weakMeridionalAction_const_mul] at hc
    have hcm : c ^ 2 * m = 1 := by
      dsimp only [c]
      rw [one_div_pow, Real.sq_sqrt ht.le]
      exact one_div_mul_cancel ht.ne'
    have hmul := mul_le_mul_of_nonneg_right hc ht.le
    have hcancel :
        (c ^ 2 * weakMeridionalAction K (fun x => r x + t * s x)
          (fun x => p x + t * q x) (fun x => z x + t * v x)) * m =
        weakMeridionalAction K (fun x => r x + t * s x)
          (fun x => p x + t * q x) (fun x => z x + t * v x) := by
      calc
        _ = (c ^ 2 * m) * weakMeridionalAction K (fun x => r x + t * s x)
            (fun x => p x + t * q x) (fun x => z x + t * v x) := by ring
        _ = _ := by rw [hcm, one_mul]
    change weakMeridionalAction K r p z * m ≤ _ at hmul
    rw [hcancel] at hmul
    simpa only [F, zero_mul, add_zero, hunit, mul_one, sub_self] using
      (sub_nonneg.mpr hmul)
  have hzero := hLocal.hasDerivAt_eq_zero hDF
  linarith only [hzero]


end RicciFlowSharpEstimate.Geometry.AreaProfile
