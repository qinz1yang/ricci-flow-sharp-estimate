/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvaturePrimitives
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh
import RicciFlowSharpEstimate.Analysis.VolterraPairing

/-!
# Curvature variation of the complete action and its normalization

The full polynomial density yields the actual curvature derivative. Proved
Volterra pairing transfers both primitive variations to a switching density.
The mass derivative is retained in normalized and Lagrange-functional statements.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff Topology

/-- Coefficient of the warp variation in the complete density derivative. -/
def curvatureWarpCoefficient (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  meridionalOperator K r x ^ 2 +
    2 * warp K x * meridionalOperator K r x * deriv (deriv r) x -
    K x * warpSlope K x * r x * deriv r x + K x ^ 2 * r x ^ 2

/-- Coefficient of the slope variation in the complete density derivative. -/
def curvatureSlopeCoefficient (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  4 * warp K x * meridionalOperator K r x * deriv r x -
    K x * r x * (warp K x * deriv r x + warpSlope K x * r x)

/-- Coefficient of the direct curvature variation in the complete density derivative. -/
def curvatureCoefficient (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * warp K x * meridionalOperator K r x * r x -
    warpSlope K x * r x * (warp K x * deriv r x + warpSlope K x * r x / 2) +
    2 * K x * warp K x * r x ^ 2

/-- Continuity of the operator requires no curvature derivative. -/
theorem meridionalOperator_continuous (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) : Continuous (meridionalOperator K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hp := hr.continuous_deriv (by simp)
  have hz := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  unfold meridionalOperator
  fun_prop

theorem curvatureWarpCoefficient_continuous (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) : Continuous (curvatureWarpCoefficient K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hp := hr.continuous_deriv (by simp)
  have hz := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  have hq := meridionalOperator_continuous K r hK hr
  unfold curvatureWarpCoefficient
  fun_prop

theorem curvatureSlopeCoefficient_continuous (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) : Continuous (curvatureSlopeCoefficient K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hp := hr.continuous_deriv (by simp)
  have hq := meridionalOperator_continuous K r hK hr
  unfold curvatureSlopeCoefficient
  fun_prop

theorem curvatureCoefficient_continuous (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) : Continuous (curvatureCoefficient K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hp := hr.continuous_deriv (by simp)
  have hq := meridionalOperator_continuous K r hK hr
  unfold curvatureCoefficient
  fun_prop

/-- The full first variation with the actual primitive variations of the same direction. -/
def curvatureFirstVariation (K r ξ : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, curvatureWarpCoefficient K r x * warpVariation ξ x +
    curvatureSlopeCoefficient K r x * warpSlopeVariation ξ x + curvatureCoefficient K r x * ξ x

private def densityQuadraticCoefficient (f b K r p z df db dK : ℝ) : ℝ :=
  let q := f * z + 2 * b * p - K * r
  let dq := df * z + 2 * db * p - dK * r
  let B := f * p + b * r / 2
  let dB := df * p + db * r / 2
  f * dq ^ 2 + 2 * df * q * dq -
    r * (dK * db * B + dK * b * dB + K * db * dB) +
    (dK ^ 2 * f + 2 * K * dK * df) * r ^ 2

private theorem density_curvature_expansion (f b K r p z df db dK t : ℝ) :
    meridionalActionDensity (f + t * df) (b + t * db) (K + t * dK) r p z =
      meridionalActionDensity f b K r p z +
        t * (((f * z + 2 * b * p - K * r) ^ 2 +
          2 * f * (f * z + 2 * b * p - K * r) * z - K * b * r * p + K ^ 2 * r ^ 2) * df +
          (4 * f * (f * z + 2 * b * p - K * r) * p - K * r * (f * p + b * r)) * db +
          (-2 * f * (f * z + 2 * b * p - K * r) * r - b * r * (f * p + b * r / 2) +
            2 * K * f * r ^ 2) * dK) +
        t ^ 2 * densityQuadraticCoefficient f b K r p z df db dK +
        t ^ 3 * meridionalActionDensity df db dK r p z := by
  unfold meridionalActionDensity densityQuadraticCoefficient
  ring

/-- Differentiation of the complete action along a curvature path, with the probe fixed. -/
theorem meridionalAction_curvature_hasDerivAt (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ) :
    HasDerivAt (fun t => meridionalAction (fun x => K x + t * ξ x) r)
      (curvatureFirstVariation K r ξ) 0 := by
  let D := fun x => meridionalActionDensity (warp K x) (warpSlope K x) (K x)
    (r x) (deriv r x) (deriv (deriv r) x)
  let V := fun x => curvatureWarpCoefficient K r x * warpVariation ξ x +
    curvatureSlopeCoefficient K r x * warpSlopeVariation ξ x + curvatureCoefficient K r x * ξ x
  let B := fun x => densityQuadraticCoefficient (warp K x) (warpSlope K x) (K x)
    (r x) (deriv r x) (deriv (deriv r) x) (warpVariation ξ x) (warpSlopeVariation ξ x) (ξ x)
  let C := fun x => meridionalActionDensity (warpVariation ξ x) (warpSlopeVariation ξ x)
    (ξ x) (r x) (deriv r x) (deriv (deriv r) x)
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hp := hr.continuous_deriv (by simp)
  have hz := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  have hdf := warpVariation_continuous ξ hξ
  have hdb := warpSlopeVariation_continuous ξ hξ
  have hα := curvatureWarpCoefficient_continuous K r hK hr
  have hβ := curvatureSlopeCoefficient_continuous K r hK hr
  have hγ := curvatureCoefficient_continuous K r hK hr
  have hD : Continuous D := meridionalAction_integrand_continuous K r hK hr
  have hV : Continuous V := by dsimp [V]; fun_prop
  have hB : Continuous B := by dsimp [B, densityQuadraticCoefficient]; fun_prop
  have hC : Continuous C := by dsimp [C, meridionalActionDensity]; fun_prop
  have heq (t : ℝ) : meridionalAction (fun x => K x + t * ξ x) r =
      meridionalAction K r + t * curvatureFirstVariation K r ξ +
        t ^ 2 * (∫ x in (0 : ℝ)..1, B x) + t ^ 3 * (∫ x in (0 : ℝ)..1, C x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, D x + t * V x + t ^ 2 * B x + t ^ 3 * C x := by
        unfold meridionalAction
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [warp_add_mul K ξ hK hξ, warpSlope_add_mul K ξ hK hξ]
        exact density_curvature_expansion _ _ _ _ _ _ _ _ _ _
      _ = _ := by
        rw [intervalIntegral.integral_add
          (((hD.intervalIntegrable 0 1).add ((hV.intervalIntegrable 0 1).const_mul t)).add
            ((hB.intervalIntegrable 0 1).const_mul (t ^ 2)))
          ((hC.intervalIntegrable 0 1).const_mul (t ^ 3)),
          intervalIntegral.integral_add
            ((hD.intervalIntegrable 0 1).add ((hV.intervalIntegrable 0 1).const_mul t))
            ((hB.intervalIntegrable 0 1).const_mul (t ^ 2)),
          intervalIntegral.integral_add (hD.intervalIntegrable 0 1)
            ((hV.intervalIntegrable 0 1).const_mul t)]
        simp only [intervalIntegral.integral_const_mul]
        rfl
  have hfun := funext heq
  rw [hfun]
  have hlin := ((hasDerivAt_id (0 : ℝ)).mul_const
    (curvatureFirstVariation K r ξ)).const_add (meridionalAction K r)
  have hquad := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x in (0 : ℝ)..1, B x)
  have hcubic := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (∫ x in (0 : ℝ)..1, C x)
  convert (hlin.add hquad).add hcubic using 1
  · funext t
    rfl
  · norm_num

/-- The full curvature switching density, before any moment multipliers or obstacle signs. -/
def curvatureSwitchingDensity (K r : ℝ → ℝ) (t : ℝ) : ℝ :=
  curvatureCoefficient K r t - 2 * ∫ x in t..1,
    (x - t) * curvatureWarpCoefficient K r x + curvatureSlopeCoefficient K r x

private theorem continuous_tail (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun t => ∫ x in t..(1 : ℝ), u x) :=
  continuous_iff_continuousAt.mpr fun t =>
    (intervalIntegral.integral_hasDerivAt_left (hu.intervalIntegrable t 1)
      (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt).continuousAt

private theorem tail_kernel_eq (u : ℝ → ℝ) (hu : Continuous u) (t : ℝ) :
    (∫ x in t..(1 : ℝ), (x - t) * u x) =
      (∫ x in t..(1 : ℝ), x * u x) - t * ∫ x in t..(1 : ℝ), u x := by
  have h1 : IntervalIntegrable (fun x : ℝ => x * u x) volume t 1 :=
    (continuous_id.mul hu).intervalIntegrable t 1
  have h2 : IntervalIntegrable (fun x => t * u x) volume t 1 :=
    (continuous_const.mul hu).intervalIntegrable t 1
  calc
    _ = ∫ x in t..(1 : ℝ), x * u x - t * u x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]

private theorem continuous_tail_kernel (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun t => ∫ x in t..(1 : ℝ), (x - t) * u x) := by
  have heq : (fun t => ∫ x in t..(1 : ℝ), (x - t) * u x) =
      fun t => (∫ x in t..(1 : ℝ), x * u x) - t * ∫ x in t..(1 : ℝ), u x :=
    funext (tail_kernel_eq u hu)
  rw [heq]
  exact (continuous_tail (fun x : ℝ => x * u x) (continuous_id.mul hu)).sub
    (continuous_id.mul (continuous_tail u hu))

private theorem switchingDensity_eq (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) (t : ℝ) :
    curvatureSwitchingDensity K r t = curvatureCoefficient K r t -
      2 * ((∫ x in t..1, (x - t) * curvatureWarpCoefficient K r x) +
        ∫ x in t..1, curvatureSlopeCoefficient K r x) := by
  have hα := curvatureWarpCoefficient_continuous K r hK hr
  have hβ := curvatureSlopeCoefficient_continuous K r hK hr
  unfold curvatureSwitchingDensity
  rw [intervalIntegral.integral_add
    (show IntervalIntegrable (fun x : ℝ => (x - t) * curvatureWarpCoefficient K r x)
      volume t 1 from ((continuous_id.sub continuous_const).mul hα).intervalIntegrable t 1)
    (hβ.intervalIntegrable t 1)]

/-- The switching density is continuous without differentiating the curvature. -/
theorem curvatureSwitchingDensity_continuous (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) : Continuous (curvatureSwitchingDensity K r) := by
  have hα := continuous_tail_kernel _ (curvatureWarpCoefficient_continuous K r hK hr)
  have hβ := continuous_tail _ (curvatureSlopeCoefficient_continuous K r hK hr)
  have hγ := curvatureCoefficient_continuous K r hK hr
  have heq := funext (switchingDensity_eq K r hK hr)
  rw [heq]
  exact hγ.sub (continuous_const.mul (hα.add hβ))

/-- Actual primitive pairing transfers the curvature variation to its switching density. -/
theorem curvatureFirstVariation_eq_integral_switching (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ) :
    curvatureFirstVariation K r ξ =
      ∫ t in (0 : ℝ)..1, curvatureSwitchingDensity K r t * ξ t := by
  have hα := curvatureWarpCoefficient_continuous K r hK hr
  have hβ := curvatureSlopeCoefficient_continuous K r hK hr
  have hγ := curvatureCoefficient_continuous K r hK hr
  have hA := continuous_tail_kernel _ hα
  have hB := continuous_tail _ hβ
  let P := fun x => ∫ t in (0 : ℝ)..x, (x - t) * ξ t
  let Q := fun x => ∫ t in (0 : ℝ)..x, ξ t
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun x =>
    (Analysis.SecondPrimitive.integral_kernel_hasDerivAt ξ hξ 0 x).continuousAt
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr fun x =>
    (hξ.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hαP : IntervalIntegrable (fun x => curvatureWarpCoefficient K r x * P x)
      volume 0 1 := (hα.mul hP).intervalIntegrable 0 1
  have hβQ : IntervalIntegrable (fun x => curvatureSlopeCoefficient K r x * Q x)
      volume 0 1 := (hβ.mul hQ).intervalIntegrable 0 1
  have hγξ : IntervalIntegrable (fun x => curvatureCoefficient K r x * ξ x)
      volume 0 1 := (hγ.mul hξ).intervalIntegrable 0 1
  have hξA : IntervalIntegrable (fun t => ξ t *
      (∫ x in t..1, (x - t) * curvatureWarpCoefficient K r x)) volume 0 1 :=
    (hξ.mul hA).intervalIntegrable 0 1
  have hξB : IntervalIntegrable (fun t => ξ t *
      (∫ x in t..1, curvatureSlopeCoefficient K r x)) volume 0 1 :=
    (hξ.mul hB).intervalIntegrable 0 1
  calc
    _ = -2 * (∫ x in (0 : ℝ)..1, curvatureWarpCoefficient K r x * P x) +
        -2 * (∫ x in (0 : ℝ)..1, curvatureSlopeCoefficient K r x * Q x) +
        ∫ x in (0 : ℝ)..1, curvatureCoefficient K r x * ξ x := by
      unfold curvatureFirstVariation
      calc
        _ = ∫ x in (0 : ℝ)..1, -2 * (curvatureWarpCoefficient K r x * P x) +
            -2 * (curvatureSlopeCoefficient K r x * Q x) + curvatureCoefficient K r x * ξ x := by
          apply intervalIntegral.integral_congr
          intro x _
          dsimp [warpVariation, warpSlopeVariation, P, Q]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add ((hαP.const_mul (-2)).add (hβQ.const_mul (-2)))
            hγξ, intervalIntegral.integral_add (hαP.const_mul (-2)) (hβQ.const_mul (-2))]
          simp only [intervalIntegral.integral_const_mul]
    _ = -2 * (∫ t in (0 : ℝ)..1, ξ t *
          (∫ x in t..1, (x - t) * curvatureWarpCoefficient K r x)) +
        -2 * (∫ t in (0 : ℝ)..1, ξ t * (∫ x in t..1, curvatureSlopeCoefficient K r x)) +
        ∫ x in (0 : ℝ)..1, curvatureCoefficient K r x * ξ x := by
      rw [Analysis.VolterraPairing.integral_mul_kernel_eq _ ξ hα hξ,
        Analysis.VolterraPairing.integral_mul_primitive_eq _ ξ hβ hξ]
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hξA.const_mul (-2)) (hξB.const_mul (-2)),
        ← intervalIntegral.integral_add ((hξA.const_mul (-2)).add (hξB.const_mul (-2))) hγξ]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [switchingDensity_eq K r hK hr]
      ring

/-- The complete curvature derivative is the switching pairing of the same direction. -/
theorem meridionalAction_curvature_hasDerivAt_switching (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ) :
    HasDerivAt (fun t => meridionalAction (fun x => K x + t * ξ x) r)
      (∫ x in (0 : ℝ)..1, curvatureSwitchingDensity K r x * ξ x) 0 := by
  rw [← curvatureFirstVariation_eq_integral_switching K r ξ hK hr hξ]
  exact meridionalAction_curvature_hasDerivAt K r ξ hK hr hξ

/-- The actual weighted mass is affine in curvature for a fixed probe. -/
theorem probeMass_curvature_add_mul (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : Continuous r) (hξ : Continuous ξ) (t : ℝ) :
    probeMass (fun x => K x + t * ξ x) r = probeMass K r +
      t * ∫ x in (0 : ℝ)..1, warpVariation ξ x * r x ^ 2 := by
  have h0 : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1 :=
    ((warp_continuous K hK).mul (hr.pow 2)).intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun x => warpVariation ξ x * r x ^ 2) volume 0 1 :=
    ((warpVariation_continuous ξ hξ).mul (hr.pow 2)).intervalIntegrable 0 1
  unfold probeMass
  calc
    _ = ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2 + t * (warpVariation ξ x * r x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [warp_add_mul K ξ hK hξ]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add h0 (h1.const_mul t), intervalIntegral.integral_const_mul]

/-- The curvature derivative of mass retains the actual warp variation. -/
theorem probeMass_curvature_hasDerivAt (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : Continuous r) (hξ : Continuous ξ) :
    HasDerivAt (fun t => probeMass (fun x => K x + t * ξ x) r)
      (∫ x in (0 : ℝ)..1, warpVariation ξ x * r x ^ 2) 0 := by
  have heq := funext (probeMass_curvature_add_mul K r ξ hK hr hξ)
  rw [heq]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const
    (∫ x in (0 : ℝ)..1, warpVariation ξ x * r x ^ 2)).const_add (probeMass K r) using 1
  · rfl
  · simp only [one_mul]

private theorem massVariation_eq_tail (r ξ : ℝ → ℝ) (hr : Continuous r)
    (hξ : Continuous ξ) :
    (∫ x in (0 : ℝ)..1, warpVariation ξ x * r x ^ 2) =
      -2 * ∫ t in (0 : ℝ)..1, ξ t * (∫ x in t..1, (x - t) * r x ^ 2) := by
  calc
    _ = -2 * ∫ x in (0 : ℝ)..1, r x ^ 2 * (∫ t in (0 : ℝ)..x, (x - t) * ξ t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [warpVariation]
      ring
    _ = _ := by
      rw [Analysis.VolterraPairing.integral_mul_kernel_eq (fun x => r x ^ 2) ξ (hr.pow 2) hξ]

/-- The switching density for action minus a mass multiplier, including the
curvature dependence of the normalization. -/
def curvatureLagrangeDensity (K r : ℝ → ℝ) (μ : ℝ) (t : ℝ) : ℝ :=
  curvatureSwitchingDensity K r t + 2 * μ * ∫ x in t..1, (x - t) * r x ^ 2

private theorem lagrangePairing_eq (K r ξ : ℝ → ℝ) (μ : ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ) :
    (∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r μ x * ξ x) =
      curvatureFirstVariation K r ξ - μ * ∫ x in (0 : ℝ)..1, warpVariation ξ x * r x ^ 2 := by
  have hS : IntervalIntegrable (fun x => curvatureSwitchingDensity K r x * ξ x) volume 0 1 :=
    ((curvatureSwitchingDensity_continuous K r hK hr).mul hξ).intervalIntegrable 0 1
  have hT : IntervalIntegrable (fun t => ξ t *
      (∫ x in t..1, (x - t) * r x ^ 2)) volume 0 1 :=
    (hξ.mul (continuous_tail_kernel _ (hr.continuous.pow 2))).intervalIntegrable 0 1
  calc
    _ = (∫ x in (0 : ℝ)..1, curvatureSwitchingDensity K r x * ξ x) +
        (2 * μ) * ∫ t in (0 : ℝ)..1, ξ t * (∫ x in t..1, (x - t) * r x ^ 2) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hS
        (hT.const_mul (2 * μ))]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [curvatureLagrangeDensity]
      ring
    _ = _ := by
      rw [← curvatureFirstVariation_eq_integral_switching K r ξ hK hr hξ,
        massVariation_eq_tail r ξ hr.continuous hξ]
      ring

/-- The Lagrange functional has the complete mass-corrected curvature derivative. -/
theorem action_sub_mass_curvature_hasDerivAt (K r ξ : ℝ → ℝ) (μ : ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ) :
    HasDerivAt (fun t => meridionalAction (fun x => K x + t * ξ x) r -
      μ * (probeMass (fun x => K x + t * ξ x) r - 1))
      (∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r μ x * ξ x) 0 := by
  rw [lagrangePairing_eq K r ξ μ hK hr hξ]
  exact (meridionalAction_curvature_hasDerivAt K r ξ hK hr hξ).sub
    (((probeMass_curvature_hasDerivAt K r ξ hK hr.continuous hξ).sub_const 1).const_mul μ)

/-- Curvature differentiation of the quotient includes the derivative of its mass. -/
theorem rayleighQuotient_curvature_hasDerivAt (K r ξ : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hξ : Continuous ξ)
    (hmass : probeMass K r ≠ 0) :
    HasDerivAt (fun t => rayleighQuotient (fun x => K x + t * ξ x) r)
      ((∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r (rayleighQuotient K r) x * ξ x) /
        probeMass K r) 0 := by
  have hm : probeMass (fun x => K x + (0 : ℝ) * ξ x) r ≠ 0 := by
    simpa only [zero_mul, add_zero] using hmass
  have hQ := (meridionalAction_curvature_hasDerivAt K r ξ hK hr hξ).fun_div
    (probeMass_curvature_hasDerivAt K r ξ hK hr.continuous hξ) hm
  simp only [zero_mul, add_zero] at hQ
  convert hQ using 1
  · rfl
  · rw [lagrangePairing_eq K r ξ (rayleighQuotient K r) hK hr hξ]
    unfold rayleighQuotient
    field_simp [hmass]


/-- The curvature derivative of the literally normalized complete action
contains the mass correction, along every zero-moment smooth direction. -/
theorem normalized_curvature_action_hasDerivAt (K r ξ : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hξ : ContDiff ℝ ∞ ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) (hmass : 0 < probeMass K r) :
    HasDerivAt (fun t => meridionalAction (fun x => K x + t * ξ x)
      (normalizedProbe (fun x => K x + t * ξ x) r))
      ((∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r (rayleighQuotient K r) x * ξ x) /
        probeMass K r) 0 := by
  have hm := (probeMass_curvature_hasDerivAt K r ξ hK.continuous hr.continuous
    hξ.continuous).continuousAt
  have hpos : ∀ᶠ t in nhds (0 : ℝ), 0 < probeMass (fun x => K x + t * ξ x) r :=
    hm.eventually (lt_mem_nhds (by simpa only [zero_mul, add_zero] using hmass))
  apply (rayleighQuotient_curvature_hasDerivAt K r ξ hK.continuous hr
    hξ.continuous hmass.ne').congr_of_eventuallyEq
  filter_upwards [hpos] with t ht
  obtain ⟨h0, h1⟩ := curvature_moments_add_mul K ξ hK.continuous hξ.continuous hξ0 hξ1 t
  rw [hK0] at h0
  rw [hK1] at h1
  exact meridionalAction_normalizedProbe (fun x => K x + t * ξ x) r
    (hK.add (contDiff_const.mul hξ)) hr h0 h1 ht


/-- Near zero, the explicit normalized curvature path has positive pre-normalization
mass, unit normalized mass and action equal to the complete Rayleigh quotient. -/
theorem eventually_normalized_curvature_variation (K r ξ : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hξ : ContDiff ℝ ∞ ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) (hmass : 0 < probeMass K r) :
    ∀ᶠ t in nhds (0 : ℝ),
      0 < probeMass (fun x => K x + t * ξ x) r ∧
      probeMass (fun x => K x + t * ξ x) (normalizedProbe (fun x => K x + t * ξ x) r) = 1 ∧
      meridionalAction (fun x => K x + t * ξ x)
        (normalizedProbe (fun x => K x + t * ξ x) r) =
          rayleighQuotient (fun x => K x + t * ξ x) r := by
  have hm := (probeMass_curvature_hasDerivAt K r ξ hK.continuous hr.continuous
    hξ.continuous).continuousAt
  have hpos : ∀ᶠ t in nhds (0 : ℝ), 0 < probeMass (fun x => K x + t * ξ x) r :=
    hm.eventually (lt_mem_nhds (by simpa only [zero_mul, add_zero] using hmass))
  filter_upwards [hpos] with t ht
  obtain ⟨h0, h1⟩ := curvature_moments_add_mul K ξ hK.continuous hξ.continuous hξ0 hξ1 t
  rw [hK0] at h0
  rw [hK1] at h1
  exact ⟨ht, probeMass_normalizedProbe _ r ht,
    meridionalAction_normalizedProbe _ r (hK.add (contDiff_const.mul hξ)) hr h0 h1 ht⟩

/-- Local curvature minima of the literally normalized action are exactly local
minima of the Rayleigh quotient, on any chosen feasible parameter set. -/
theorem isLocalMinOn_normalized_curvature_iff (K r ξ : ℝ → ℝ) (S : Set ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hξ : ContDiff ℝ ∞ ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) (hmass : 0 < probeMass K r) :
    IsLocalMinOn (fun t => meridionalAction (fun x => K x + t * ξ x)
        (normalizedProbe (fun x => K x + t * ξ x) r)) S 0 ↔
      IsLocalMinOn (fun t => rayleighQuotient (fun x => K x + t * ξ x) r) S 0 := by
  have heq : (fun t => meridionalAction (fun x => K x + t * ξ x)
      (normalizedProbe (fun x => K x + t * ξ x) r)) =ᶠ[nhds (0 : ℝ)]
      (fun t => rayleighQuotient (fun x => K x + t * ξ x) r) :=
    (eventually_normalized_curvature_variation K r ξ hK hr hξ hK0 hK1 hξ0 hξ1 hmass).mono
      fun _ h => h.2.2
  constructor
  · intro h
    exact IsMinFilter.congr h (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds
  · intro h
    exact IsMinFilter.congr h (heq.symm.filter_mono nhdsWithin_le_nhds) heq.symm.eq_of_nhds

end RicciFlowSharpEstimate.Geometry.AreaProfile
