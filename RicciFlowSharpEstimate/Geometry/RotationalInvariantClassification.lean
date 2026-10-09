/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothQuotient
import RicciFlowSharpEstimate.Geometry.RotationalInvariantProfiles
import RicciFlowSharpEstimate.Geometry.RotationalZonalReduction
import RicciFlowSharpEstimate.Geometry.RotationalHaarDissipation

/-!
# Global invariant one-forms and the actual zonal Haar action

The global height coefficients come from genuine smooth pole pullbacks. Division
by the metric profile takes place only on its positive physical interval; smooth
extensions retain the original global meridional and azimuthal producers.
-/

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace RotationalProfile.PoleData

/-- Every invariant smooth one-form is the sum of the actual meridional and
azimuthal sections for globally smooth real probes, including both poles. -/
theorem exists_smooth_zonal_decomposition_of_rotationInvariant (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      h = D.meridionalOneForm r hr + D.azimuthalOneForm s hs := by
  obtain ⟨P, Q, hP, hQ, hrepr⟩ := exists_smooth_height_azimuthal_profiles h hinv
  obtain ⟨r, hr, hra⟩ := Analysis.exists_contDiff_mul_eq_on_Icc (-1) 1 (by norm_num)
    D.a P D.a_contDiff hP (fun v hv => (D.a_pos v hv).ne')
  obtain ⟨s, hs, hsb⟩ := Analysis.exists_contDiff_mul_eq_on_Icc (-1) 1 (by norm_num)
    D.b Q D.b_contDiff hQ (fun v hv => (D.b_pos v hv).ne')
  refine ⟨r, s, hr, hs, ?_⟩
  ext x slots
  have heq : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  rw [heq]
  change h x (fun _ : Fin 1 => slots 0) =
    D.meridionalOneForm r hr x (fun _ : Fin 1 => slots 0) +
      D.azimuthalOneForm s hs x (fun _ : Fin 1 => slots 0)
  rw [hrepr, meridionalOneForm_apply, azimuthalOneForm_apply,
    hra _ (sphereHeight_mem_Icc x), hsb _ (sphereHeight_mem_Icc x)]

/-- The genuine Haar projector has globally smooth meridional and azimuthal probes. -/
theorem exists_smooth_zonal_decomposition_rotationalAverage (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      rotationalAverage h = D.meridionalOneForm r hr + D.azimuthalOneForm s hs :=
  D.exists_smooth_zonal_decomposition_of_rotationInvariant (rotationalAverage h)
    (fun z => diffeomorphTensorPullback_circle_rotationalAverage z h)

/-- The exact zonal probes of the actual Haar average reduce its contribution
in the original complete dissipation split, without any sign assertion. -/
theorem exists_haar_zonal_dissipation (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      rotationalAverage h = D.meridionalOneForm r hr + D.azimuthalOneForm s hs ∧
      oneFormDissipation D.metric h =
        2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) +
          oneFormDissipation D.metric (h - rotationalAverage h) := by
  obtain ⟨r, s, hr, hs, hrepr⟩ := D.exists_smooth_zonal_decomposition_rotationalAverage h
  refine ⟨r, s, hr, hs, hrepr, ?_⟩
  rw [D.oneFormDissipation_haar_split h, hrepr, D.oneFormDissipation_zonal]

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
