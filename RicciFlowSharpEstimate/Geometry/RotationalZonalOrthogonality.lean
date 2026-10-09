/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalReflection
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality

/-!
# Reflection orthogonality for the complete action

The actual meridian reflection is an isometry, fixes the meridional section and
reverses the azimuthal section. The full four-term pairing therefore vanishes.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

namespace RotationalProfile.PoleData

/-- The genuine covector pullback fixes every smooth meridional form. -/
theorem diffeomorphTensorPullback_meridional_reflection (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    diffeomorphTensorPullback meridianReflectionSphereDiffeo (D.meridionalOneForm r hr) =
      D.meridionalOneForm r hr := by
  apply DFunLike.ext
  intro x
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by funext i; exact congrArg slots (Fin.eq_zero i)
  rw [hs, diffeomorphTensorPullback_apply]
  exact D.meridionalOneForm_meridianReflectionSphereDiffeo r hr x (slots 0)

/-- The same genuine covector pullback reverses every smooth azimuthal form. -/
theorem diffeomorphTensorPullback_azimuthal_reflection (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    diffeomorphTensorPullback meridianReflectionSphereDiffeo (D.azimuthalOneForm r hr) =
      (-1 : ℝ) • D.azimuthalOneForm r hr := by
  apply DFunLike.ext
  intro x
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by funext i; exact congrArg slots (Fin.eq_zero i)
  rw [hs, diffeomorphTensorPullback_apply]
  change _ = -1 * D.azimuthalOneForm r hr x (fun _ : Fin 1 => slots 0)
  rw [neg_one_mul]
  exact D.azimuthalOneForm_meridianReflectionSphereDiffeo r hr x (slots 0)

/-- The two smooth zonal sectors are orthogonal for the entire four-term pairing. -/
theorem oneFormDissipationPairing_meridional_azimuthal (D : PoleData)
    (r s : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    oneFormDissipationPairing D.metric (D.meridionalOneForm r hr)
      (D.azimuthalOneForm s hs) = 0 := by
  have h := oneFormDissipationPairing_diffeomorphTensorPullback_of_isometry D.metric
    meridianReflectionSphereDiffeo D.pullbackMetric_meridianReflectionSphereDiffeo
    (D.meridionalOneForm r hr) (D.azimuthalOneForm s hs)
  rw [D.diffeomorphTensorPullback_meridional_reflection,
    D.diffeomorphTensorPullback_azimuthal_reflection, oneFormDissipationPairing_smul_right] at h
  linarith

/-- The complete action splits between the actual meridional and azimuthal sections. -/
theorem oneFormDissipation_meridional_add_azimuthal (D : PoleData)
    (r s : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    oneFormDissipation D.metric (D.meridionalOneForm r hr + D.azimuthalOneForm s hs) =
      oneFormDissipation D.metric (D.meridionalOneForm r hr) +
        oneFormDissipation D.metric (D.azimuthalOneForm s hs) := by
  rw [oneFormDissipation_add, D.oneFormDissipationPairing_meridional_azimuthal]
  ring

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
