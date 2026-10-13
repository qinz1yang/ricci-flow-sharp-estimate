/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakAreaAction
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh
import RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra

/-!
# Polarization and exact variations of the complete weak area action

The pairing polarizes the complete six-entry density, retaining its mixed
term and both potential terms. The weak derivative graph and the actual
coefficient bounds prove integrability before integral linearity is used.
The resulting action and mass variations are exact quadratic polynomials.
No curvature derivative, endpoint trace, or stationarity assumption occurs.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The symmetric polarization density of the complete weak area action. -/
def weakMeridionalPairingDensity
    (K r p z s q u : ℝ → ℝ) (x : ℝ) : ℝ :=
  warp K x * weakMeridionalOperator K r p z x * weakMeridionalOperator K s q u x -
    K x * warpSlope K x * warp K x * (r x * q x + s x * p x) / 2 +
    (K x ^ 2 * warp K x - K x * warpSlope K x ^ 2 / 2) * r x * s x

/-- The actual complete weak action pairing on the normalized area interval. -/
def weakMeridionalPairing (K r p z s q u : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, weakMeridionalPairingDensity K r p z s q u x

/-- The complete weak pairing is symmetric in its two supplied weak jets. -/
theorem weakMeridionalPairing_symm (K r p z s q u : ℝ → ℝ) :
    weakMeridionalPairing K r p z s q u = weakMeridionalPairing K s q u r p z := by
  unfold weakMeridionalPairing
  apply intervalIntegral.integral_congr
  intro x _
  unfold weakMeridionalPairingDensity
  ring

/-- The diagonal of the complete weak pairing is exactly the original action. -/
@[simp]
theorem weakMeridionalPairing_self (K r p z : ℝ → ℝ) :
    weakMeridionalPairing K r p z r p z = weakMeridionalAction K r p z := by
  unfold weakMeridionalPairing weakMeridionalAction
  apply intervalIntegral.integral_congr
  intro x _
  unfold weakMeridionalPairingDensity weakMeridionalOperator meridionalActionDensity
  ring

/-- Simultaneous scalar multiplication of all three jet entries scales the
complete weak action by the square of the scalar. -/
theorem weakMeridionalAction_const_mul (K r p z : ℝ → ℝ) (c : ℝ) :
    weakMeridionalAction K (fun x ↦ c * r x) (fun x ↦ c * p x) (fun x ↦ c * z x) =
      c ^ 2 * weakMeridionalAction K r p z := by
  unfold weakMeridionalAction
  calc
    _ = ∫ x in (0 : ℝ)..1, c ^ 2 *
        meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold meridionalActionDensity
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

section CompleteAction

variable (K r p z s q u : ℝ → ℝ) (hi : ℝ)
    (hgraphR : Analysis.HasParabolicWeakDerivatives r p z)
    (hgraphS : Analysis.HasParabolicWeakDerivatives s q u)
    (hhi : 0 ≤ hi)
    (hK : AEStronglyMeasurable K areaμ)
    (hf : AEStronglyMeasurable (warp K) areaμ)
    (hb : AEStronglyMeasurable (warpSlope K) areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ hi)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x)))
    (hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2)

include hgraphR hgraphS hhi hK hf hb hKbox hfbox hbbox

/-- Three genuinely integrable complete densities give integrability of their
polarization on the weak derivative graph. -/
theorem integrable_weakMeridionalPairingDensity_of_warp_bounds :
    Integrable (weakMeridionalPairingDensity K r p z s q u) areaμ := by
  have hR := integrable_weakMeridionalActionDensity_of_warp_bounds
    K r p z hi hgraphR hhi hK hf hb hKbox hfbox hbbox
  have hS := integrable_weakMeridionalActionDensity_of_warp_bounds
    K s q u hi hgraphS hhi hK hf hb hKbox hfbox hbbox
  have hRS := integrable_weakMeridionalActionDensity_of_warp_bounds
    K (fun x ↦ r x + s x) (fun x ↦ p x + q x) (fun x ↦ z x + u x)
    hi (hgraphR.add hgraphS) hhi hK hf hb hKbox hfbox hbbox
  apply (((hRS.sub hR).sub hS).const_mul (1 / 2 : ℝ)).congr
  filter_upwards [] with x
  dsimp only [Pi.sub_apply, weakMeridionalPairingDensity, weakMeridionalOperator,
    meridionalActionDensity]
  ring

/-- The complete weak pairing is integrable on the original interval. -/
theorem weakMeridionalPairing_intervalIntegrable_of_warp_bounds :
    IntervalIntegrable (weakMeridionalPairingDensity K r p z s q u) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  exact integrable_weakMeridionalPairingDensity_of_warp_bounds
    K r p z s q u hi hgraphR hgraphS hhi hK hf hb hKbox hfbox hbbox

/-- The exact quadratic variation of the complete action on the genuine weak
derivative graph, with all mixed and potential terms retained. -/
theorem weakMeridionalAction_add_mul (t : ℝ) :
    weakMeridionalAction K (fun x ↦ r x + t * s x)
      (fun x ↦ p x + t * q x) (fun x ↦ z x + t * u x) =
        weakMeridionalAction K r p z +
          2 * t * weakMeridionalPairing K r p z s q u +
          t ^ 2 * weakMeridionalAction K s q u := by
  have hR := weakMeridionalAction_intervalIntegrable_of_warp_bounds
    K r p z hi hgraphR hhi hK hf hb hKbox hfbox hbbox
  have hS := weakMeridionalAction_intervalIntegrable_of_warp_bounds
    K s q u hi hgraphS hhi hK hf hb hKbox hfbox hbbox
  have hP := weakMeridionalPairing_intervalIntegrable_of_warp_bounds
    K r p z s q u hi hgraphR hgraphS hhi hK hf hb hKbox hfbox hbbox
  unfold weakMeridionalAction weakMeridionalPairing
  calc
    _ = ∫ x in (0 : ℝ)..1,
        meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x) +
          (2 * t) * weakMeridionalPairingDensity K r p z s q u x +
          t ^ 2 * meridionalActionDensity
            (warp K x) (warpSlope K x) (K x) (s x) (q x) (u x) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold meridionalActionDensity weakMeridionalPairingDensity weakMeridionalOperator
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hR.add (hP.const_mul (2 * t)))
        (hS.const_mul (t ^ 2)),
        intervalIntegral.integral_add hR (hP.const_mul (2 * t))]
      simp only [intervalIntegral.integral_const_mul]

/-- The derivative of the complete weak action along its affine jet variation
at every real parameter, obtained from its exact quadratic polynomial. -/
theorem weakMeridionalAction_hasDerivAt (t : ℝ) :
    HasDerivAt (fun v ↦ weakMeridionalAction K (fun x ↦ r x + v * s x)
      (fun x ↦ p x + v * q x) (fun x ↦ z x + v * u x))
      (2 * weakMeridionalPairing K r p z s q u +
        2 * t * weakMeridionalAction K s q u) t := by
  have heq :
      (fun v ↦ weakMeridionalAction K (fun x ↦ r x + v * s x)
        (fun x ↦ p x + v * q x) (fun x ↦ z x + v * u x)) =
      (fun v ↦ weakMeridionalAction K r p z +
        2 * v * weakMeridionalPairing K r p z s q u +
        v ^ 2 * weakMeridionalAction K s q u) := by
    funext v
    exact weakMeridionalAction_add_mul K r p z s q u hi hgraphR hgraphS
      hhi hK hf hb hKbox hfbox hbbox v
  rw [heq]
  convert (((hasDerivAt_id t).const_mul 2).mul_const
    (weakMeridionalPairing K r p z s q u)).const_add
      (weakMeridionalAction K r p z) |>.add
        (((hasDerivAt_id t).pow 2).mul_const (weakMeridionalAction K s q u)) using 1
  · funext v
    rfl
  · norm_num

end CompleteAction

private theorem ae_norm_warp_le_of_parabolic_bound
    (K : ℝ → ℝ) (hi : ℝ) (hhi : 0 ≤ hi)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x))) :
    ∀ᵐ x ∂areaμ, ‖warp K x‖ ≤ hi := by
  filter_upwards [hfbox] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  have hw : x * (1 - x) ≤ 1 := by
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  exact hx.2.trans (mul_le_of_le_one_right hhi hw)

section Mass

variable (K r s : ℝ → ℝ) (hi : ℝ)
    (hR : MemLp r 2 areaμ) (hS : MemLp s 2 areaμ)
    (hhi : 0 ≤ hi)
    (hf : AEStronglyMeasurable (warp K) areaμ)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x)))

include hR hhi hf hfbox

/-- The mass density is integrable for an L² probe and actual warp bound. -/
theorem integrable_probeMassDensity_of_warp_bounds :
    Integrable (fun x ↦ warp K x * r x ^ 2) areaμ :=
  hR.integrable_sq.bdd_mul hf (ae_norm_warp_le_of_parabolic_bound K hi hhi hfbox)

/-- The original interval mass is integrable for an L² probe and actual warp bound. -/
theorem probeMass_intervalIntegrable_of_warp_bounds :
    IntervalIntegrable (fun x ↦ warp K x * r x ^ 2) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  exact integrable_probeMassDensity_of_warp_bounds K r hi hR hhi hf hfbox

include hS

/-- The weighted mass pairing is integrable for two L² probes. -/
theorem integrable_probeMassPairing_of_warp_bounds :
    Integrable (fun x ↦ warp K x * s x * r x) areaμ := by
  have h := (hS.integrable_mul hR).bdd_mul
    hf (ae_norm_warp_le_of_parabolic_bound K hi hhi hfbox)
  simpa only [Pi.mul_apply, mul_assoc] using h

/-- The same mass pairing is integrable on the original normalized interval. -/
theorem probeMassPairing_intervalIntegrable_of_warp_bounds :
    IntervalIntegrable (fun x ↦ warp K x * s x * r x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  exact integrable_probeMassPairing_of_warp_bounds
    K r s hi hR hS hhi hf hfbox

/-- The exact quadratic mass expansion for L² probes with the actual warp bound. -/
theorem probeMass_add_mul_of_warp_bounds (t : ℝ) :
    probeMass K (fun x ↦ r x + t * s x) = probeMass K r +
      2 * t * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) + t ^ 2 * probeMass K s := by
  have hiR := probeMass_intervalIntegrable_of_warp_bounds K r hi hR hhi hf hfbox
  have hiS := probeMass_intervalIntegrable_of_warp_bounds K s hi hS hhi hf hfbox
  have hP := probeMassPairing_intervalIntegrable_of_warp_bounds
    K r s hi hR hS hhi hf hfbox
  unfold probeMass
  calc
    _ = ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2 +
        (2 * t) * (warp K x * s x * r x) + t ^ 2 * (warp K x * s x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hiR.add (hP.const_mul (2 * t)))
        (hiS.const_mul (t ^ 2)),
        intervalIntegral.integral_add hiR (hP.const_mul (2 * t))]
      simp only [intervalIntegral.integral_const_mul]

/-- The mass derivative at every parameter of an affine L² probe variation. -/
theorem probeMass_hasDerivAt_of_warp_bounds (t : ℝ) :
    HasDerivAt (fun v ↦ probeMass K (fun x ↦ r x + v * s x))
      (2 * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) + 2 * t * probeMass K s) t := by
  have heq : (fun v ↦ probeMass K (fun x ↦ r x + v * s x)) =
      (fun v ↦ probeMass K r +
        2 * v * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) + v ^ 2 * probeMass K s) := by
    funext v
    exact probeMass_add_mul_of_warp_bounds
      K r s hi hR hS hhi hf hfbox v
  rw [heq]
  convert (((hasDerivAt_id t).const_mul 2).mul_const
    (∫ x in (0 : ℝ)..1, warp K x * s x * r x)).const_add (probeMass K r) |>.add
      (((hasDerivAt_id t).pow 2).mul_const (probeMass K s)) using 1
  · funext v
    rfl
  · norm_num

end Mass

end RicciFlowSharpEstimate.Geometry.AreaProfile
