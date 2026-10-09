/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCoordinates
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

/-!
# Global meridional and azimuthal one-forms

The smooth sections `a(z) r(z) dz` and `b(z) s(z) (-y dx + x dy)` use actual
ambient coordinate differentials on the fixed sphere. Their cylinder evaluations
are `a(v) r(v) dv` and `warp a(v) s(v) dθ`; both sections vanish at the poles.

The global coordinate construction adapts Ziyang Qin's historical
`Geometry/Surface/RotationalZonalOneForms.lean` to the pinned release.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RicciIdentity
open Set
open scoped Manifold ContDiff RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The genuine smooth differential of an ambient coordinate restricted to the sphere. -/
def sphereCoordinateOneForm (i : Fin 3) :
    OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  duSec (I := 𝓡 2) (innerCoordFun (n := 2) (EuclideanSpace.single i (1 : ℝ)))
    (innerCoordFun (n := 2) (EuclideanSpace.single i (1 : ℝ))).contMDiff

/-- Evaluation of a coordinate differential is the coordinate of the actual ambient tangent. -/
@[simp] theorem sphereCoordinateOneForm_apply (i : Fin 3) (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    sphereCoordinateOneForm i x (fun _ : Fin 1 => v) = (dIncl (n := 2) x v) i := by
  rw [sphereCoordinateOneForm, duSec_apply, differential1FormFun_apply_eq_mvfderiv,
    mvfderiv_real_eq_mfderiv, mfderiv_innerCoordFun]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

/-- The third ambient coordinate differential is the accepted height one-form. -/
@[simp] theorem sphereCoordinateOneForm_two : sphereCoordinateOneForm 2 = heightOneForm := rfl

/-- The height one-form reads the third coordinate of the actual ambient tangent. -/
theorem heightOneForm_apply_dIncl (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    heightOneForm x (fun _ : Fin 1 => v) = (dIncl (n := 2) x v) 2 := by
  rw [← sphereCoordinateOneForm_two, sphereCoordinateOneForm_apply]

/-- The globally smooth angular covector `κ = -y dx + x dy`. -/
def sphereAzimuthalOneForm : OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
      (fun x : RotationalSphere =>
        -innerCoordFun (n := 2) (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) x)
      (innerCoordFun (n := 2) (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))).contMDiff.neg
      (sphereCoordinateOneForm 0) +
    tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
      (innerCoordFun (n := 2) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      (innerCoordFun (n := 2) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).contMDiff
      (sphereCoordinateOneForm 1)

/-- The angular covector retains its literal ambient-coordinate expression. -/
@[simp] theorem sphereAzimuthalOneForm_apply (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    sphereAzimuthalOneForm x (fun _ : Fin 1 => v) =
      -(x : EuclideanSpace ℝ (Fin 3)) 1 * (dIncl (n := 2) x v) 0 +
        (x : EuclideanSpace ℝ (Fin 3)) 0 * (dIncl (n := 2) x v) 1 := by
  simp [sphereAzimuthalOneForm, tensor0SField_smulByFun_apply,
    innerCoordFun, EuclideanSpace.inner_single_left]

/-- The angular covector evaluates to `(1-v²) dθ` on the actual cylinder derivative. -/
theorem sphereAzimuthalOneForm_cylinderMap_mfderiv (q : cylinderDomain)
    (V : EuclideanSpace ℝ (Fin 2)) :
    sphereAzimuthalOneForm (cylinderMap q) (fun _ : Fin 1 =>
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V) =
        (1 - q.val 0 ^ 2) * V 1 := by
  rw [sphereAzimuthalOneForm_apply, cylinderMap_coe, cylinderMap_dIncl_mfderiv]
  change -(Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) *
      ((-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) * V 0 -
        (Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) * V 1) +
    (Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) *
      ((-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) * V 0 +
        (Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) * V 1) = _
  have hrad : 0 ≤ 1 - q.val 0 ^ 2 := by
    have h := q.property
    change -1 < q.val 0 ∧ q.val 0 < 1 at h
    nlinarith
  calc
    _ = Real.sqrt (1 - q.val 0 ^ 2) ^ 2 *
        (Real.cos (q.val 1) ^ 2 + Real.sin (q.val 1) ^ 2) * V 1 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, Real.sq_sqrt hrad, mul_one]

private theorem horizontal_coordinates_eq_zero_of_height_sq_eq_one
    (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    (x : EuclideanSpace ℝ (Fin 3)) 0 = 0 ∧
      (x : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by
  have hn : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have hs := EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin 3))
  rw [hn] at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change 1 ^ 2 = (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
    ((x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2) at hs
  rw [sphereHeight_apply] at hx
  constructor <;> nlinarith [sq_nonneg ((x : EuclideanSpace ℝ (Fin 3)) 0),
    sq_nonneg ((x : EuclideanSpace ℝ (Fin 3)) 1)]

/-- The smooth angular covector vanishes at either pole. -/
theorem sphereAzimuthalOneForm_eq_zero_at_pole (x : RotationalSphere)
    (hx : sphereHeight x ^ 2 = 1) : sphereAzimuthalOneForm x = 0 := by
  apply ContinuousMultilinearMap.ext
  intro slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  rw [hslots]
  change sphereAzimuthalOneForm x (fun _ : Fin 1 => slots 0) = 0
  rw [sphereAzimuthalOneForm_apply]
  obtain ⟨h0, h1⟩ := horizontal_coordinates_eq_zero_of_height_sq_eq_one x hx
  simp [h0, h1]

/-- The smooth height differential vanishes at either pole. -/
theorem heightOneForm_eq_zero_at_pole (x : RotationalSphere)
    (hx : sphereHeight x ^ 2 = 1) : heightOneForm x = 0 := by
  apply ContinuousMultilinearMap.ext
  intro slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  rw [hslots]
  have h := HeightMetricCoefficients.heightOneForm_sq_le x (slots 0)
  rw [hx, sub_self, zero_mul] at h
  change heightOneForm x (fun _ : Fin 1 => slots 0) = 0
  nlinarith [sq_nonneg (heightOneForm x (fun _ : Fin 1 => slots 0))]

namespace RotationalProfile.PoleData

/-- The global smooth meridional section `a(z) r(z) dz`. -/
def meridionalOneForm (D : PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
    (fun x : RotationalSphere => D.a (sphereHeight x) * r (sphereHeight x))
    ((D.a_contDiff.comp_contMDiff sphereHeight_contMDiff).mul
      (hr.comp_contMDiff sphereHeight_contMDiff)) heightOneForm

/-- The meridional producer retains its exact scalar multiple of the height differential. -/
@[simp] theorem meridionalOneForm_apply (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere)
    (slots : Fin 1 → TangentSpace (𝓡 2) x) :
    D.meridionalOneForm r hr x slots =
      (D.a (sphereHeight x) * r (sphereHeight x)) * heightOneForm x slots := by
  rw [meridionalOneForm, tensor0SField_smulByFun_apply]
  rfl

/-- The meridional form on a genuine tangent vector, in ambient coordinates. -/
theorem meridionalOneForm_apply_dIncl (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    D.meridionalOneForm r hr x (fun _ : Fin 1 => v) =
      D.a (sphereHeight x) * r (sphereHeight x) * (dIncl (n := 2) x v) 2 := by
  rw [meridionalOneForm_apply, heightOneForm_apply_dIncl]

/-- The actual cylinder pullback of the meridional form is `a(v) r(v) dv`. -/
theorem meridionalOneForm_cylinderMap_mfderiv (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (q : cylinderDomain) (V : EuclideanSpace ℝ (Fin 2)) :
    D.meridionalOneForm r hr (cylinderMap q) (fun _ : Fin 1 =>
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V) =
        D.a (q.val 0) * r (q.val 0) * V 0 := by
  rw [meridionalOneForm_apply_dIncl, sphereHeight_cylinderMap, cylinderMap_dIncl_mfderiv]
  rfl

/-- The global smooth azimuthal section `b(z) s(z) κ`. -/
def azimuthalOneForm (D : PoleData) (s : ℝ → ℝ) (hs : ContDiff ℝ ∞ s) :
    OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
    (fun x : RotationalSphere => D.b (sphereHeight x) * s (sphereHeight x))
    ((D.b_contDiff.comp_contMDiff sphereHeight_contMDiff).mul
      (hs.comp_contMDiff sphereHeight_contMDiff)) sphereAzimuthalOneForm

/-- The azimuthal producer retains its exact scalar multiple of the angular covector. -/
@[simp] theorem azimuthalOneForm_apply (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) (x : RotationalSphere)
    (slots : Fin 1 → TangentSpace (𝓡 2) x) :
    D.azimuthalOneForm s hs x slots =
      (D.b (sphereHeight x) * s (sphereHeight x)) * sphereAzimuthalOneForm x slots := by
  rw [azimuthalOneForm, tensor0SField_smulByFun_apply]
  rfl

/-- The azimuthal form on a genuine tangent vector, in ambient coordinates. -/
theorem azimuthalOneForm_apply_dIncl (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    D.azimuthalOneForm s hs x (fun _ : Fin 1 => v) =
      (D.b (sphereHeight x) * s (sphereHeight x)) *
        (-(x : EuclideanSpace ℝ (Fin 3)) 1 * (dIncl (n := 2) x v) 0 +
          (x : EuclideanSpace ℝ (Fin 3)) 0 * (dIncl (n := 2) x v) 1) := by
  rw [azimuthalOneForm_apply, sphereAzimuthalOneForm_apply]

/-- The actual cylinder pullback of the azimuthal form is `warp a(v) s(v) dθ`. -/
theorem azimuthalOneForm_cylinderMap_mfderiv (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) (q : cylinderDomain) (V : EuclideanSpace ℝ (Fin 2)) :
    D.azimuthalOneForm s hs (cylinderMap q) (fun _ : Fin 1 =>
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V) =
        warp D.a (q.val 0) * s (q.val 0) * V 1 := by
  rw [azimuthalOneForm_apply, sphereHeight_cylinderMap,
    sphereAzimuthalOneForm_cylinderMap_mfderiv, D.warp_factor]
  ring

/-- Every smooth meridional probe gives a section vanishing at both poles. -/
theorem meridionalOneForm_eq_zero_at_pole (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    D.meridionalOneForm r hr x = 0 := by
  rw [meridionalOneForm, tensor0SField_smulByFun_apply, heightOneForm_eq_zero_at_pole x hx,
    smul_zero]

/-- Every smooth azimuthal probe gives a section vanishing at both poles. -/
theorem azimuthalOneForm_eq_zero_at_pole (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    D.azimuthalOneForm s hs x = 0 := by
  rw [azimuthalOneForm, tensor0SField_smulByFun_apply,
    sphereAzimuthalOneForm_eq_zero_at_pole x hx, smul_zero]

/-- The constant unit meridional probe is nonzero for every accepted profile. -/
theorem meridionalOneForm_one_ne_zero (D : PoleData) :
    D.meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 := by
  intro h
  let q : cylinderDomain := ⟨0, by constructor <;> norm_num⟩
  let V : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hev := D.meridionalOneForm_cylinderMap_mfderiv (fun _ => 1) contDiff_const q V
  rw [h] at hev
  have ha := D.a_pos 0 (by constructor <;> norm_num)
  simp [q, V] at hev
  exact ha.ne' hev.symm

/-- The constant unit azimuthal probe is nonzero for every accepted profile. -/
theorem azimuthalOneForm_one_ne_zero (D : PoleData) :
    D.azimuthalOneForm (fun _ => 1) contDiff_const ≠ 0 := by
  intro h
  let q : cylinderDomain := ⟨0, by constructor <;> norm_num⟩
  let V : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have hev := D.azimuthalOneForm_cylinderMap_mfderiv (fun _ => 1) contDiff_const q V
  rw [h] at hev
  have hw := D.cylinderMap_warp_pos q
  simp [q, V] at hev hw
  exact hw.ne' hev.symm

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
