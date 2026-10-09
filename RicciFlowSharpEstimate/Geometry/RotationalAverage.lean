/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.TensorIntervalIntegral
import RicciFlowSharpEstimate.Geometry.RotationalTensorAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The genuine normalized rotational Haar projection

The average integrates the actual covector pullbacks in each native tensor fiber.
The globally smooth producer includes the poles. Its construction is independent
of the reciprocal-curvature profile.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry
open MeasureTheory
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The normalized Haar average of the original smooth covariant tensor. -/
def rotationalAverage {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s :=
  (2 * Real.pi)⁻¹ • tensorIntervalIntegral
    (fun θ => diffeomorphTensorPullback (angleRotation θ) A)
    (contMDiff_diffeomorphTensorPullback_angleRotation A) 0 (2 * Real.pi)

/-- Evaluation retains the integral of the actual tensor pullbacks. -/
theorem rotationalAverage_eval {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) :
    rotationalAverage A x v = (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi, diffeomorphTensorPullback (angleRotation θ) A x v := by
  change (2 * Real.pi)⁻¹ *
    (tensorIntervalIntegral (fun θ => diffeomorphTensorPullback (angleRotation θ) A)
      (contMDiff_diffeomorphTensorPullback_angleRotation A) 0 (2 * Real.pi) x v) = _
  rw [tensorIntervalIntegral_eval]

/-- Literal normalized covector pullback, with the rotation derivative in every slot. -/
theorem rotationalAverage_apply {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) :
    rotationalAverage A x v = (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        A (angleRotation θ x) (fun i => mfderiv (𝓡 2) (𝓡 2) (angleRotation θ) x (v i)) := by
  simp only [rotationalAverage_eval, diffeomorphTensorPullback_apply]

private theorem orbit_integrable {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) (a b : ℝ) :
    IntervalIntegrable (fun θ => diffeomorphTensorPullback (angleRotation θ) A x v)
      volume a b :=
  intervalIntegrable_diffeomorphTensorPullback_family_eval angleRotation
    angleRotation_contMDiff A x v volume a b

/-- The Haar average is additive on the native smooth tensor fields. -/
theorem rotationalAverage_add {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (A + B) = rotationalAverage A + rotationalAverage B := by
  apply DFunLike.ext
  intro x
  ext v
  change rotationalAverage (A + B) x v = rotationalAverage A x v + rotationalAverage B x v
  simp only [rotationalAverage_eval, diffeomorphTensorPullback_add]
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
      diffeomorphTensorPullback (angleRotation θ) A x v +
        diffeomorphTensorPullback (angleRotation θ) B x v) = _
  rw [intervalIntegral.integral_add (orbit_integrable A x v _ _) (orbit_integrable B x v _ _)]
  ring

/-- The Haar average commutes with real scalar multiplication. -/
theorem rotationalAverage_smul {s : ℕ} (c : ℝ)
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (c • A) = c • rotationalAverage A := by
  apply DFunLike.ext
  intro x
  ext v
  change rotationalAverage (c • A) x v = c * rotationalAverage A x v
  simp only [rotationalAverage_eval, diffeomorphTensorPullback_smul]
  change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
      c * diffeomorphTensorPullback (angleRotation θ) A x v) = _
  rw [intervalIntegral.integral_const_mul]
  ring

@[simp] theorem rotationalAverage_zero (s : ℕ) :
    rotationalAverage
      (0 : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) = 0 := by
  simpa only [zero_smul] using rotationalAverage_smul (s := s) 0 0

theorem rotationalAverage_sub {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (A - B) = rotationalAverage A - rotationalAverage B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B, rotationalAverage_add, rotationalAverage_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

private theorem integral_periodic_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (φ : ℝ) : (∫ θ in (0 : ℝ)..2 * Real.pi, f (θ + φ)) = ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hf.intervalIntegral_add_eq φ 0

private theorem orbit_periodic {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) :
    Function.Periodic (fun θ => diffeomorphTensorPullback (angleRotation θ) A x v)
      (2 * Real.pi) := by
  intro θ
  exact congrArg (fun B => B x v) (diffeomorphTensorPullback_angleRotation_periodic A θ)

/-- Averaging is unchanged by first rotating the original tensor. -/
theorem rotationalAverage_diffeomorphTensorPullback (φ : ℝ) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (diffeomorphTensorPullback (angleRotation φ) A) = rotationalAverage A := by
  apply DFunLike.ext
  intro x
  ext v
  simp only [rotationalAverage_eval, ← diffeomorphTensorPullback_angleRotation_add]
  rw [integral_periodic_shift _ (orbit_periodic A x v)]

/-- The actual averaged tensor is rotation invariant. -/
theorem diffeomorphTensorPullback_rotationalAverage (φ : ℝ) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (angleRotation φ) (rotationalAverage A) = rotationalAverage A := by
  apply DFunLike.ext
  intro x
  ext v
  rw [diffeomorphTensorPullback_apply, rotationalAverage_eval, rotationalAverage_eval]
  have h (θ : ℝ) :
      diffeomorphTensorPullback (angleRotation θ) A (angleRotation φ x)
        (fun i => mfderiv (𝓡 2) (𝓡 2) (angleRotation φ) x (v i)) =
      diffeomorphTensorPullback (angleRotation (θ + φ)) A x v := by
    rw [add_comm, diffeomorphTensorPullback_angleRotation_add]
    exact (diffeomorphTensorPullback_apply (angleRotation φ)
      (diffeomorphTensorPullback (angleRotation θ) A) x v).symm
  simp_rw [h]
  rw [integral_periodic_shift _ (orbit_periodic A x v)]

/-- The average fixes every tensor invariant under the actual rotations. -/
theorem rotationalAverage_eq_self_of_invariant {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (hA : ∀ θ, diffeomorphTensorPullback (angleRotation θ) A = A) :
    rotationalAverage A = A := by
  apply DFunLike.ext
  intro x
  ext v
  simp_rw [rotationalAverage_eval, hA]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- The genuine smooth Haar average is idempotent. -/
theorem rotationalAverage_idempotent {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (rotationalAverage A) = rotationalAverage A :=
  rotationalAverage_eq_self_of_invariant _
    (fun φ => diffeomorphTensorPullback_rotationalAverage φ A)

/-- The actual complementary tensor has zero Haar average. -/
theorem rotationalAverage_sub_average {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage (A - rotationalAverage A) = 0 := by
  rw [rotationalAverage_sub, rotationalAverage_idempotent, sub_self]

/-- The actual averaged tensor is invariant under every element of the native circle. -/
theorem diffeomorphTensorPullback_circle_rotationalAverage (z : Circle) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (circleSphereDiffeo z) (rotationalAverage A) =
      rotationalAverage A := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  exact diffeomorphTensorPullback_rotationalAverage θ A

/-- The range of the projector is precisely the tensors invariant under the actual circle action. -/
theorem rotationalAverage_eq_self_iff {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    rotationalAverage A = A ↔
      ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) A = A := by
  constructor
  · intro h z
    calc
      diffeomorphTensorPullback (circleSphereDiffeo z) A =
          diffeomorphTensorPullback (circleSphereDiffeo z) (rotationalAverage A) :=
        congrArg (diffeomorphTensorPullback (circleSphereDiffeo z)) h.symm
      _ = rotationalAverage A := diffeomorphTensorPullback_circle_rotationalAverage z A
      _ = A := h
  · intro h
    exact rotationalAverage_eq_self_of_invariant A (fun θ => h (Circle.exp θ))

namespace RotationalProfile.PoleData

/-- Every genuine smooth meridional form is fixed by the actual Haar average. -/
theorem rotationalAverage_meridionalOneForm (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    rotationalAverage (D.meridionalOneForm r hr) = D.meridionalOneForm r hr := by
  apply rotationalAverage_eq_self_of_invariant
  intro θ
  apply DFunLike.ext
  intro x
  ext v
  have hv : v = fun _ : Fin 1 => v 0 := by funext i; exact congrArg v (Fin.eq_zero i)
  rw [hv, diffeomorphTensorPullback_apply,
    D.meridionalOneForm_apply, D.meridionalOneForm_apply]
  change D.a (sphereHeight (circleSphereDiffeo (Circle.exp θ) x)) *
      r (sphereHeight (circleSphereDiffeo (Circle.exp θ) x)) *
      heightOneForm (sphereDiffeo (n := 2) (axisRotation (Circle.exp θ)) x)
        (fun _ : Fin 1 => mfderiv (𝓡 2) (𝓡 2)
          (sphereDiffeo (n := 2) (axisRotation (Circle.exp θ))) x (v 0)) = _
  rw [sphereHeight_circleSphereDiffeo, heightOneForm_sphereDiffeo
    (axisRotation (Circle.exp θ)) (axisRotation_fix_heightAxis (Circle.exp θ))]

/-- The projector has a genuine nonzero one-form in its image for every produced metric. -/
theorem rotationalAverage_meridional_one_ne_zero (D : PoleData) :
    rotationalAverage (D.meridionalOneForm (fun _ => 1) contDiff_const) ≠ 0 := by
  rw [D.rotationalAverage_meridionalOneForm]
  exact D.meridionalOneForm_one_ne_zero

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
