/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ManifoldIntervalIntegral
import RicciFlowSharpEstimate.Geometry.RotationalCircleAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The normalized scalar rotational average

The scalar average integrates the original function along the actual angle rotations.
It preserves smoothness and is an invariant projection. At either genuine pole,
the entire orbit is fixed, so zero angular mean forces the original value to vanish.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry MeasureTheory
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The normalized scalar integral along the concrete rotations of the unit sphere. -/
def rotationalScalarAverage (u : RotationalSphere → ℝ) (x : RotationalSphere) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, u (angleRotation θ x)

/-- Averaging a smooth scalar function gives a smooth scalar function on the whole sphere. -/
theorem rotationalScalarAverage_contMDiff {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (rotationalScalarAverage u) :=
  contMDiff_const.mul (Analysis.contMDiff_intervalIntegral (⊤ : ℕ∞) 0 (2 * Real.pi)
    (hu.comp angleRotation_contMDiff))

private theorem scalar_orbit_intervalIntegrable {u : RotationalSphere → ℝ}
    (hu : Continuous u) (x : RotationalSphere) (a b : ℝ) :
    IntervalIntegrable (fun θ => u (angleRotation θ x)) volume a b :=
  (hu.comp (angleRotation_contMDiff.continuous.comp
    (continuous_id.prodMk continuous_const))).intervalIntegrable a b

/-- The scalar average is additive on continuous functions. -/
theorem rotationalScalarAverage_add {u v : RotationalSphere → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    rotationalScalarAverage (u + v) = rotationalScalarAverage u + rotationalScalarAverage v := by
  funext x
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
    u (angleRotation θ x) + v (angleRotation θ x)) = _
  rw [intervalIntegral.integral_add (scalar_orbit_intervalIntegrable hu x _ _)
    (scalar_orbit_intervalIntegrable hv x _ _)]
  exact mul_add _ _ _

/-- The scalar average commutes with subtraction of continuous functions. -/
theorem rotationalScalarAverage_sub {u v : RotationalSphere → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    rotationalScalarAverage (u - v) = rotationalScalarAverage u - rotationalScalarAverage v := by
  funext x
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
    u (angleRotation θ x) - v (angleRotation θ x)) = _
  rw [intervalIntegral.integral_sub (scalar_orbit_intervalIntegrable hu x _ _)
    (scalar_orbit_intervalIntegrable hv x _ _)]
  exact mul_sub _ _ _

/-- Multiplication by a real constant commutes with the scalar average. -/
theorem rotationalScalarAverage_smul (c : ℝ) (u : RotationalSphere → ℝ) :
    rotationalScalarAverage (c • u) = c • rotationalScalarAverage u := by
  funext x
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
    c * u (angleRotation θ x)) = c * ((2 * Real.pi)⁻¹ * _)
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The normalized average fixes every constant function. -/
@[simp] theorem rotationalScalarAverage_const (c : ℝ) :
    rotationalScalarAverage (fun _ => c) = fun _ => c := by
  funext x
  simp only [rotationalScalarAverage, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

@[simp] theorem rotationalScalarAverage_zero :
    rotationalScalarAverage (0 : RotationalSphere → ℝ) = 0 :=
  rotationalScalarAverage_const 0

/-- The constant function one is a fixed nonzero scalar profile. -/
@[simp] theorem rotationalScalarAverage_one :
    rotationalScalarAverage (1 : RotationalSphere → ℝ) = 1 :=
  rotationalScalarAverage_const 1

private theorem scalar_orbit_periodic (u : RotationalSphere → ℝ) (x : RotationalSphere) :
    Function.Periodic (fun θ => u (angleRotation θ x)) (2 * Real.pi) := by
  intro θ
  change u (angleRotation (θ + 2 * Real.pi) x) = u (angleRotation θ x)
  rw [angleRotation_periodic θ]

private theorem scalar_integral_periodic_shift (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) (φ : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (θ + φ)) = ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hf.intervalIntegral_add_eq φ 0

/-- The scalar average is invariant under every actual angle rotation. -/
theorem rotationalScalarAverage_angleRotation (u : RotationalSphere → ℝ)
    (φ : ℝ) (x : RotationalSphere) :
    rotationalScalarAverage u (angleRotation φ x) = rotationalScalarAverage u x := by
  simp only [rotationalScalarAverage, ← angleRotation_add]
  rw [scalar_integral_periodic_shift _ (scalar_orbit_periodic u x)]

/-- Rotating the original scalar function does not change its average. -/
theorem rotationalScalarAverage_comp_angleRotation (u : RotationalSphere → ℝ) (φ : ℝ) :
    rotationalScalarAverage (fun x => u (angleRotation φ x)) = rotationalScalarAverage u := by
  funext x
  simp only [rotationalScalarAverage, ← angleRotation_add]
  simp_rw [add_comm φ]
  rw [scalar_integral_periodic_shift _ (scalar_orbit_periodic u x)]

/-- The scalar average fixes every function invariant under the concrete rotations. -/
theorem rotationalScalarAverage_eq_self_of_invariant (u : RotationalSphere → ℝ)
    (hu : ∀ θ x, u (angleRotation θ x) = u x) : rotationalScalarAverage u = u := by
  funext x
  simp only [rotationalScalarAverage, hu, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- The literal normalized scalar integral is an idempotent projection. -/
theorem rotationalScalarAverage_idempotent (u : RotationalSphere → ℝ) :
    rotationalScalarAverage (rotationalScalarAverage u) = rotationalScalarAverage u :=
  rotationalScalarAverage_eq_self_of_invariant _ (rotationalScalarAverage_angleRotation u)

private theorem angleRotation_fixed_at_pole (θ : ℝ) (x : RotationalSphere)
    (hx : sphereHeight x ^ 2 = 1) : angleRotation θ x = x := by
  have hn : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have hs := EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin 3))
  rw [hn] at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change 1 ^ 2 = (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
    ((x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2) at hs
  rw [sphereHeight_apply] at hx
  have h0 : (x : EuclideanSpace ℝ (Fin 3)) 0 = 0 := by nlinarith
  have h1 : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by nlinarith
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [angleRotation, h0, h1]

/-- At either actual pole the scalar average equals the original scalar value. -/
theorem rotationalScalarAverage_eq_at_pole (u : RotationalSphere → ℝ)
    (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    rotationalScalarAverage u x = u x := by
  simp only [rotationalScalarAverage, angleRotation_fixed_at_pole _ x hx,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- Zero angular mean forces the original scalar function to vanish at both poles. -/
theorem rotationalScalarAverage_eq_zero_at_pole {u : RotationalSphere → ℝ}
    (hu : rotationalScalarAverage u = 0) (x : RotationalSphere)
    (hx : sphereHeight x ^ 2 = 1) : u x = 0 := by
  rw [← rotationalScalarAverage_eq_at_pole u x hx, hu]
  rfl

end RicciFlowSharpEstimate.Geometry
