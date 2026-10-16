/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalQuadraticPinching
import RicciFlowSharpEstimate.Geometry.AreaSlopeCalibration
import RicciFlowSharpEstimate.Geometry.AreaThresholdMinimum

/-! # A strict gap above the explicit quadratic-pinching safe cap -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry
open AreaProfile

/-- The unrestricted original all-form threshold is strictly larger than
the quadratic-pinching cap. The sharp value is not identified by this bound. -/
theorem quadratic_pinching_lt_rotationalThreshold :
    (1 + Real.sqrt (3 / 2) : ℝ) < rotationalThreshold := by
  by_contra! hle
  obtain ⟨K, r, p, z, h, _, _, _, _, hzero, _⟩ :=
    exists_zero_action_recoverable_area_minimizer
  have hpos := h.action_pos_of_quadratic_pinching one_le_rotationalThreshold hle
  linarith only [hpos, hzero]

end RicciFlowSharpEstimate.Geometry
