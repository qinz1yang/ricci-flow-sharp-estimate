/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization

/-!
# Integrable Euler coefficients of the complete weak probe equation

The coefficients retain the actual curvature primitives, meridional operator,
mixed term and potential terms. The complete pairing with the three genuine
smooth test jets of `1`, `x` and `x²` isolates their integrability. No classical
derivatives of the weak probe or additional endpoint assumptions are required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The coefficient of the second test derivative in the complete weak probe equation. -/
def weakProbeSecondCoefficient (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  warp K x ^ 2 * weakMeridionalOperator K r p z x

/-- The coefficient of the first test derivative in the complete weak probe equation. -/
def weakProbeFirstCoefficient (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * warp K x * warpSlope K x * weakMeridionalOperator K r p z x -
    K x * warpSlope K x * warp K x * r x / 2

/-- The coefficient of the test function in the complete weak probe equation,
including the mass multiplier and both original potential terms. -/
def weakProbeZerothCoefficient (K r p z : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  -warp K x * K x * weakMeridionalOperator K r p z x -
    K x * warpSlope K x * warp K x * p x / 2 +
    (K x ^ 2 * warp K x - K x * warpSlope K x ^ 2 / 2) * r x -
    lam * warp K x * r x

/-- The full pairing density minus its mass term is exactly the three Euler
coefficients paired with the supplied test jet. This identity is pointwise
algebra and imposes no regularity assumptions on either jet. -/
theorem weakMeridionalPairingDensity_eq_probe_coefficients
    (K r p z s t u : ℝ → ℝ) (lam x : ℝ) :
    weakMeridionalPairingDensity K r p z s t u x -
        lam * warp K x * r x * s x =
      weakProbeSecondCoefficient K r p z x * u x +
        weakProbeFirstCoefficient K r p z x * t x +
        weakProbeZerothCoefficient K r p z lam x * s x := by
  unfold weakMeridionalPairingDensity weakProbeSecondCoefficient
    weakProbeFirstCoefficient weakProbeZerothCoefficient weakMeridionalOperator
  ring

private theorem integrable_probe_lagrange_density
    {C : ℝ} {K r p z s t u : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hs : Analysis.HasParabolicWeakDerivatives s t u) (lam : ℝ) :
    Integrable (fun x => weakMeridionalPairingDensity K r p z s t u x -
      lam * warp K x * r x * s x) areaμ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGeo := h.geometry_bounds hC
  have hf : AEStronglyMeasurable (warp K) areaμ :=
    ((hGeo.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
  have hb : AEStronglyMeasurable (warpSlope K) areaμ :=
    ((hGeo.2.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
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
  have hPair := integrable_weakMeridionalPairingDensity_of_warp_bounds
    K r p z s t u (2 * C) h.2.1 hs (by positivity)
    h.1.aestronglyMeasurable hf hb hKbox hfbox hbbox
  have hMass := integrable_probeMassPairing_of_warp_bounds
    K s r (2 * C) hs.memLp h.2.1.memLp (by positivity) hf hfbox
  apply (hPair.sub (hMass.const_mul lam)).congr
  filter_upwards [] with x
  dsimp only [Pi.sub_apply]
  ring

private theorem integrable_coordinate_mul {v : ℝ → ℝ}
    (hv : Integrable v areaμ) : Integrable (fun x => x * v x) areaμ := by
  apply hv.bdd_mul (c := 1) continuous_id.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [id_eq, Real.norm_eq_abs, abs_of_pos hx.1]
  exact hx.2.le

private theorem constant_probe_weak_graph :
    Analysis.HasParabolicWeakDerivatives
      (fun _ : ℝ => 1) (fun _ => 0) (fun _ => 0) := by
  simpa only [deriv_const'] using Analysis.hasParabolicWeakDerivatives_of_contDiff
    (show ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) from contDiff_const)

private theorem coordinate_probe_weak_graph :
    Analysis.HasParabolicWeakDerivatives
      (fun x : ℝ => x) (fun _ => 1) (fun _ => 0) := by
  simpa only [deriv_id'', deriv_const'] using
    Analysis.hasParabolicWeakDerivatives_of_contDiff
      (show ContDiff ℝ 2 (fun x : ℝ => x) from contDiff_id)

private theorem square_probe_weak_graph :
    Analysis.HasParabolicWeakDerivatives
      (fun x : ℝ => x ^ 2) (fun x => 2 * x) (fun _ => 2) := by
  have hD : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x
    simp
  have hDD : deriv (fun x : ℝ => 2 * x) = fun _ => 2 := by
    funext x
    simp
  simpa only [hD, hDD] using Analysis.hasParabolicWeakDerivatives_of_contDiff
    (show ContDiff ℝ 2 (fun x : ℝ => x ^ 2) from contDiff_id.pow 2)

/-- Every recoverable weak competitor has three integrable full probe Euler
coefficients for every real mass multiplier. Their integrability follows from
the complete action pairing and the genuine parabolic weak derivative graph. -/
theorem IsRecoverableAreaCompetitor.weak_probe_euler_coefficients_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (lam : ℝ) :
    Integrable (weakProbeSecondCoefficient K r p z) areaμ ∧
      Integrable (weakProbeFirstCoefficient K r p z) areaμ ∧
      Integrable (weakProbeZerothCoefficient K r p z lam) areaμ := by
  have hConstant := integrable_probe_lagrange_density hC h constant_probe_weak_graph lam
  have hCoordinate := integrable_probe_lagrange_density hC h coordinate_probe_weak_graph lam
  have hSquare := integrable_probe_lagrange_density hC h square_probe_weak_graph lam
  have hZeroth : Integrable (weakProbeZerothCoefficient K r p z lam) areaμ := by
    apply hConstant.congr
    filter_upwards [] with x
    rw [weakMeridionalPairingDensity_eq_probe_coefficients]
    ring
  have hXZeroth := integrable_coordinate_mul hZeroth
  have hFirst : Integrable (weakProbeFirstCoefficient K r p z) areaμ := by
    apply (hCoordinate.sub hXZeroth).congr
    filter_upwards [] with x
    dsimp only [Pi.sub_apply]
    rw [weakMeridionalPairingDensity_eq_probe_coefficients]
    ring
  have hXFirst := integrable_coordinate_mul hFirst
  have hXXZeroth := integrable_coordinate_mul hXZeroth
  have hSecond : Integrable (weakProbeSecondCoefficient K r p z) areaμ := by
    apply (((hSquare.sub (hXFirst.const_mul 2)).sub hXXZeroth).const_mul
      (1 / 2 : ℝ)).congr
    filter_upwards [] with x
    dsimp only [Pi.sub_apply]
    rw [weakMeridionalPairingDensity_eq_probe_coefficients]
    ring
  exact ⟨hSecond, hFirst, hZeroth⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
