/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormRotationDissipation
import RicciFlowSharpEstimate.Geometry.RotationalHodgeRotation
import RicciFlowSharpEstimate.Geometry.RotationalMeridionalReduction
import RicciFlowSharpEstimate.Geometry.RotationalZonalOrthogonality

/-!
# Exact zonal reduction for the genuine rotational sphere metric

The produced parallel area tensor gives the actual Hodge rotation. Together with
meridian-reflection orthogonality, it reduces the complete action of both sectors.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

namespace RotationalProfile.PoleData

/-- Hodge rotation for the actual metric and its explicitly produced outward area form. -/
def hodgeRotation (D : PoleData) (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  oneFormAreaContraction D.metric D.areaForm h

/-- The rotation retains the actual metric sharp and area-form evaluation. -/
@[simp] theorem hodgeRotation_apply (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere)
    (Y : TangentSpace (𝓡 2) x) :
    D.hodgeRotation h x (fun _ : Fin 1 => Y) =
      D.areaForm x (vec2 (cotangentSharp D.metric x (h x)) Y) :=
  oneFormAreaContraction_apply D.metric D.areaForm h x Y

/-- This actual Hodge rotation preserves the complete action of every smooth form. -/
theorem oneFormDissipation_hodgeRotation (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric (D.hodgeRotation h) = oneFormDissipation D.metric h :=
  oneFormDissipation_oneFormAreaContraction D.metric D.areaForm
    D.areaForm_alternating D.areaForm_normSq h

/-- Outward Hodge rotation sends the original meridional form to minus its azimuthal form. -/
theorem hodgeRotation_meridionalOneForm (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    D.hodgeRotation (D.meridionalOneForm r hr) = (-1 : ℝ) • D.azimuthalOneForm r hr := by
  apply DFunLike.ext
  intro x
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by funext i; exact congrArg slots (Fin.eq_zero i)
  rw [hs, hodgeRotation_apply]
  change D.areaForm x (vec2
    (inverseMetricSharpFib D.metric x (D.meridionalOneForm r hr x)) (slots 0)) =
      -1 * D.azimuthalOneForm r hr x (fun _ : Fin 1 => slots 0)
  rw [neg_one_mul]
  exact D.areaForm_inverseMetricSharpFib_meridionalOneForm r hr x (slots 0)

/-- The complete azimuthal and meridional actions agree for the same probe. -/
theorem oneFormDissipation_azimuthal_eq_meridional (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    oneFormDissipation D.metric (D.azimuthalOneForm r hr) =
      oneFormDissipation D.metric (D.meridionalOneForm r hr) := by
  have h := D.oneFormDissipation_hodgeRotation (D.meridionalOneForm r hr)
  rw [D.hodgeRotation_meridionalOneForm r hr, oneFormDissipation_smul] at h
  simpa using h

/-- Exact azimuthal reduction for the actual smooth global section. -/
theorem oneFormDissipation_azimuthal (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    oneFormDissipation D.metric (D.azimuthalOneForm r hr) =
      2 * Real.pi * D.meridionalAction r := by
  rw [D.oneFormDissipation_azimuthal_eq_meridional, D.oneFormDissipation_meridional]

/-- The exact full zonal identity, without equatorial symmetry or independently chosen jets. -/
theorem oneFormDissipation_zonal (D : PoleData) (r s : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    oneFormDissipation D.metric (D.meridionalOneForm r hr + D.azimuthalOneForm s hs) =
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) := by
  rw [D.oneFormDissipation_meridional_add_azimuthal,
    D.oneFormDissipation_meridional, D.oneFormDissipation_azimuthal]
  ring

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
