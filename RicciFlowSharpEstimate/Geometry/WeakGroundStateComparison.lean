/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableMultiplicativeStationarity
import RicciFlowSharpEstimate.Geometry.AreaGroundStateComparison

/-!
# Complete Picone identity at the actual weak minimum

The square multiplier is a proved feasible weak direction. Its stationarity
identity replaces the complete pairing by the actual action times physical
mass. The remainder is integrable because it equals a difference of genuinely
integrable complete densities. No sign of the weak probe or operator is assumed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual recoverable minimum obeys the complete Picone identity for
every smooth multiplier. Its signed remainder is genuinely integrable.
This equality alone does not assert a sign or coverage of arbitrary probes. -/
theorem IsRecoverableAreaCompetitor.picone_identity_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    let R := fun x =>
      warp K x * (warp K x * r x * deriv (deriv u) x +
        2 * (warp K x * p x + warpSlope K x * r x) * deriv u x) ^ 2 -
        2 * warp K x ^ 2 * r x * weakMeridionalOperator K r p z x * deriv u x ^ 2
    IntervalIntegrable R volume 0 1 ∧
      weakMeridionalAction K (fun x => r x * u x)
        (fun x => p x * u x + r x * deriv u x)
        (fun x => z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x) -
        weakMeridionalAction K r p z * probeMass K (fun x => r x * u x) =
        ∫ x in (0 : ℝ)..1, R x := by
  dsimp only
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGeo := h.geometry_bounds hC
  have hgraph := h.2.1
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
  have huD := (contDiff_infty_iff_deriv.mp hu).2
  have hd : deriv (fun x => u x ^ 2) = fun x => 2 * u x * deriv u x := by
    funext x
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_def] using
      ((hu.differentiable (by simp) x).hasDerivAt.pow 2).deriv
  have hdd : deriv (deriv (fun x => u x ^ 2)) =
      fun x => 2 * (deriv u x ^ 2 + u x * deriv (deriv u) x) := by
    rw [hd]
    funext x
    convert (((hu.differentiable (by simp) x).hasDerivAt.const_mul 2).mul
      (huD.differentiable (by simp) x).hasDerivAt).deriv using 1
    ring
  let S := fun x => r x * u x
  let P := fun x => p x * u x + r x * deriv u x
  let Z := fun x => z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x
  let T := fun x => r x * u x ^ 2
  let Q := fun x => p x * u x ^ 2 + 2 * r x * u x * deriv u x
  let V := fun x => z x * u x ^ 2 + 4 * p x * u x * deriv u x +
    2 * r x * (deriv u x ^ 2 + u x * deriv (deriv u) x)
  have hQ : (fun x => p x * u x ^ 2 + r x * deriv (fun y => u y ^ 2) x) = Q := by
    rw [hd]
    funext x
    dsimp only [Q]
    ring
  have hV : (fun x => z x * u x ^ 2 + 2 * p x * deriv (fun y => u y ^ 2) x +
      r x * deriv (deriv (fun y => u y ^ 2)) x) = V := by
    rw [hdd, hd]
    funext x
    dsimp only [V]
    ring
  have hS : Analysis.HasParabolicWeakDerivatives S P Z := hgraph.mul_contDiff u hu
  have hT : Analysis.HasParabolicWeakDerivatives T Q V := by
    have ht := hgraph.mul_contDiff (fun x => u x ^ 2) (hu.pow 2)
    rw [hQ, hV] at ht
    exact ht
  have hA := weakMeridionalAction_intervalIntegrable_of_warp_bounds
    K S P Z (2 * C) hS (by positivity) h.1.aestronglyMeasurable hf hb hKbox hfbox hbbox
  have hB := weakMeridionalPairing_intervalIntegrable_of_warp_bounds
    K r p z T Q V (2 * C) hgraph hT
    (by positivity) h.1.aestronglyMeasurable hf hb hKbox hfbox hbbox
  have hpoint (x : ℝ) :=
    weakMeridionalPicone_density_identity K r p z u (deriv u) (deriv (deriv u)) x
  have hInt := hA.sub hB
  have hR : IntervalIntegrable (fun x =>
      warp K x * (warp K x * r x * deriv (deriv u) x +
        2 * (warp K x * p x + warpSlope K x * r x) * deriv u x) ^ 2 -
        2 * warp K x ^ 2 * r x * weakMeridionalOperator K r p z x * deriv u x ^ 2)
      volume 0 1 := by
    apply hInt.congr
    intro x _
    exact hpoint x
  have hp := h.weak_probe_mul_equation_of_minimum hC hmin (fun x => u x ^ 2) (hu.pow 2)
  rw [hQ, hV] at hp
  have hmass : (∫ x in (0 : ℝ)..1, warp K x * (r x * u x ^ 2) * r x) =
      probeMass K S := by
    unfold probeMass
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [S]
    ring
  rw [hmass] at hp
  refine ⟨hR, ?_⟩
  change weakMeridionalAction K S P Z - weakMeridionalAction K r p z * probeMass K S = _
  rw [← hp]
  unfold weakMeridionalAction weakMeridionalPairing
  rw [← intervalIntegral.integral_sub hA hB]
  apply intervalIntegral.integral_congr
  intro x _
  exact hpoint x

end RicciFlowSharpEstimate.Geometry.AreaProfile
