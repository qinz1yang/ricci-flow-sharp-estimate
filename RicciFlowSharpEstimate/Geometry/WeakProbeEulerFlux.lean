/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SecondOrderWeakEuler
import RicciFlowSharpEstimate.Geometry.WeakProbeEulerCoefficients
import RicciFlowSharpEstimate.Geometry.AreaMomentMultipliers

/-!
# Actual Euler fluxes and natural pole laws of the joint weak minimum

The unrestricted smooth probe equation produces two canonical integral
primitives. They are absolutely continuous on the closed physical interval,
have zero endpoint traces, and satisfy genuine almost-everywhere derivative
laws. The leading primitive represents the literal weighted weak operator;
division by the positive interior warp gives its continuous representative.
No endpoint value or derivative condition is imposed on the probe itself.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual integral Euler flux, with the full mass-corrected source. -/
def weakProbeEulerFlux (K r p z : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  -(∫ t in (0 : ℝ)..x, weakProbeZerothCoefficient K r p z lam t)

/-- The actual primitive representing the leading weighted Euler coefficient. -/
def weakProbeEulerMomentum (K r p z : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, weakProbeFirstCoefficient K r p z t + weakProbeEulerFlux K r p z lam t

private theorem probe_euler_identity_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (s : ℝ → ℝ) (hs : ContDiff ℝ ∞ s) :
    (∫ x in (0 : ℝ)..1,
      weakProbeSecondCoefficient K r p z x * deriv (deriv s) x +
        weakProbeFirstCoefficient K r p z x * deriv s x +
        weakProbeZerothCoefficient K r p z (weakMeridionalAction K r p z) x * s x) = 0 := by
  let lam := weakMeridionalAction K r p z
  let L : ℝ → ℝ := fun x =>
    weakProbeSecondCoefficient K r p z x * deriv (deriv s) x +
      weakProbeFirstCoefficient K r p z x * deriv s x +
      weakProbeZerothCoefficient K r p z lam x * s x
  obtain ⟨hU, hV, hH⟩ := h.weak_probe_euler_coefficients_integrable hC lam
  have hUI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hU
  have hVI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hV
  have hHI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hH
  have hds : ContDiff ℝ ∞ (deriv s) := (contDiff_infty_iff_deriv.mp hs).2
  have hLI : IntervalIntegrable L volume 0 1 :=
    ((hUI.mul_continuousOn (hds.continuous_deriv (by simp)).continuousOn).add
      (hVI.mul_continuousOn (hs.continuous_deriv (by simp)).continuousOn)).add
      (hHI.mul_continuousOn hs.continuous.continuousOn)
  have hrI : IntervalIntegrable r volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hf : ContinuousOn (warp K) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using (h.geometry_bounds hC).1
  have hMI : IntervalIntegrable (fun x => warp K x * r x * s x) volume 0 1 :=
    (hrI.continuousOn_mul hf).mul_continuousOn hs.continuous.continuousOn
  have hB : weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
      (∫ x in (0 : ℝ)..1, L x) + lam * (∫ x in (0 : ℝ)..1, warp K x * r x * s x) := by
    unfold weakMeridionalPairing
    calc
      _ = ∫ x in (0 : ℝ)..1, L x + lam * (warp K x * r x * s x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [L]
        linear_combination weakMeridionalPairingDensity_eq_probe_coefficients
          K r p z s (deriv s) (deriv (deriv s)) lam x
      _ = _ := by
        rw [intervalIntegral.integral_add hLI (hMI.const_mul lam),
          intervalIntegral.integral_const_mul]
  have hm : (∫ x in (0 : ℝ)..1, warp K x * s x * r x) =
      ∫ x in (0 : ℝ)..1, warp K x * r x * s x := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have heq := h.weak_probe_equation_of_minimum hC hmin s hs
  rw [hB, hm] at heq
  change (∫ x in (0 : ℝ)..1, L x) = 0
  change (∫ x in (0 : ℝ)..1, L x) + lam * _ = lam * _ at heq
  linarith

/-- The actual joint minimum has absolutely continuous Euler fluxes with
natural zero traces at both poles. Their derivatives and weighted operator
identity hold a.e.; the operator has a continuous representative on the open
physical interval. These are consequences of the unrestricted probe equation. -/
theorem IsRecoverableAreaCompetitor.probe_euler_flux_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    weakProbeSecondCoefficient K r p z =ᵐ[areaμ] weakProbeEulerMomentum K r p z lam ∧
      AbsolutelyContinuousOnInterval (weakProbeEulerFlux K r p z lam) 0 1 ∧
      AbsolutelyContinuousOnInterval (weakProbeEulerMomentum K r p z lam) 0 1 ∧
      weakProbeEulerFlux K r p z lam 0 = 0 ∧ weakProbeEulerFlux K r p z lam 1 = 0 ∧
      weakProbeEulerMomentum K r p z lam 0 = 0 ∧ weakProbeEulerMomentum K r p z lam 1 = 0 ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (weakProbeEulerFlux K r p z lam)
        (-weakProbeZerothCoefficient K r p z lam x) x) ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (weakProbeEulerMomentum K r p z lam)
        (weakProbeFirstCoefficient K r p z x + weakProbeEulerFlux K r p z lam x) x) ∧
      ContinuousOn (fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2)
        (Ioo (0 : ℝ) 1) ∧
      weakMeridionalOperator K r p z =ᵐ[areaμ]
        (fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2) := by
  let lam := weakMeridionalAction K r p z
  obtain ⟨hU, hV, hH⟩ := h.weak_probe_euler_coefficients_integrable hC lam
  have hEuler := probe_euler_identity_of_minimum hC h hmin
  obtain ⟨hUA, hPAC, hAAC, hP0, hP1, hA0, hA1, hPD, hAD⟩ :=
    Analysis.second_order_weak_euler_flux 0 1 zero_le_one
      (weakProbeSecondCoefficient K r p z) (weakProbeFirstCoefficient K r p z)
      (weakProbeZerothCoefficient K r p z lam) hU hV hH hEuler
  change weakProbeSecondCoefficient K r p z =ᵐ[areaμ]
    weakProbeEulerMomentum K r p z lam at hUA
  change AbsolutelyContinuousOnInterval (weakProbeEulerMomentum K r p z lam) 0 1 at hAAC
  have hGeo := h.geometry_bounds hC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hGeo.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hAcont : ContinuousOn (weakProbeEulerMomentum K r p z lam) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hAAC.continuousOn
  refine ⟨hUA, hPAC, hAAC, hP0, hP1, hA0, hA1, hPD, hAD, ?_, ?_⟩
  · exact (hAcont.mono Ioo_subset_Icc_self).div
      ((hGeo.1.mono Ioo_subset_Icc_self).pow 2)
      (fun x hx => pow_ne_zero 2 (hfpos x hx).ne')
  · filter_upwards [hUA, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    apply (eq_div_iff (pow_ne_zero 2 (hfpos x hxI).ne')).mpr
    simpa only [weakProbeSecondCoefficient, mul_comm] using hx

/-- A cap alone supplies the actual physical joint minimum, its moment
multipliers and a.e. complementarity, together with canonical absolutely
continuous Euler fluxes, natural pole laws, and the continuous interior
representative of its actual weak meridional operator. -/
theorem exists_recoverable_area_minimizer_with_natural_flux (C : ℝ) (hC : 1 ≤ C) :
    ∃ (K r p z : ℝ → ℝ) (κ Λ a b : ℝ),
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
      0 < κ ∧ (1 < C → κ < 2 ∧ 2 < Λ) ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C ∧
      (C = 1 → K =ᵐ[areaμ] fun _ => 2) ∧
      (∀ᵐ x ∂areaμ,
        (κ < K x → weakCurvatureAdjoint K r p z (smoothAreaInfimum C) x - a - b * x ≤ 0) ∧
        (K x < Λ → 0 ≤ weakCurvatureAdjoint K r p z (smoothAreaInfimum C) x - a - b * x)) ∧
      (weakProbeSecondCoefficient K r p z =ᵐ[areaμ]
        weakProbeEulerMomentum K r p z (smoothAreaInfimum C) ∧
      AbsolutelyContinuousOnInterval (weakProbeEulerFlux K r p z (smoothAreaInfimum C)) 0 1 ∧
      AbsolutelyContinuousOnInterval (weakProbeEulerMomentum K r p z (smoothAreaInfimum C)) 0 1 ∧
      weakProbeEulerFlux K r p z (smoothAreaInfimum C) 0 = 0 ∧
      weakProbeEulerFlux K r p z (smoothAreaInfimum C) 1 = 0 ∧
      weakProbeEulerMomentum K r p z (smoothAreaInfimum C) 0 = 0 ∧
      weakProbeEulerMomentum K r p z (smoothAreaInfimum C) 1 = 0 ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (weakProbeEulerFlux K r p z (smoothAreaInfimum C))
        (-weakProbeZerothCoefficient K r p z (smoothAreaInfimum C) x) x) ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (weakProbeEulerMomentum K r p z (smoothAreaInfimum C))
        (weakProbeFirstCoefficient K r p z x +
          weakProbeEulerFlux K r p z (smoothAreaInfimum C) x) x) ∧
      ContinuousOn (fun x => weakProbeEulerMomentum K r p z (smoothAreaInfimum C) x / warp K x ^ 2)
        (Ioo (0 : ℝ) 1) ∧
      weakMeridionalOperator K r p z =ᵐ[areaμ]
        (fun x => weakProbeEulerMomentum K r p z (smoothAreaInfimum C) x / warp K x ^ 2)) := by
  obtain ⟨K, r, p, z, κ, Λ, a, b, h, hrc, hpc, hnz, heq, hmin, hprobe, hW,
    hκ, hstrict, hbox, hratio, hround, hsign⟩ :=
    exists_recoverable_area_minimizer_with_moment_multipliers C hC
  refine ⟨K, r, p, z, κ, Λ, a, b, h, hrc, hpc, hnz, heq, hmin, hprobe, hW,
    hκ, hstrict, hbox, hratio, hround, hsign, ?_⟩
  simpa only [heq] using h.probe_euler_flux_of_minimum hC hmin

end RicciFlowSharpEstimate.Geometry.AreaProfile
