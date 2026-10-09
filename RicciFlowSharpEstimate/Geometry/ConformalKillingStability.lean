/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConstantZonalAction
import RicciFlowSharpEstimate.Variational.HemisphereStability

/-!
# Geometric hemisphere stability for constant conformal-Killing probes

The original produced metric and constant zonal section give the exact normalized
hemisphere deficit. Its full reciprocal logarithm satisfies all three hemisphere
stability estimates, including the reflection factor four. Zero coefficients
produce the zero section and zero action without a profile conclusion.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set Variational RicciFlowSharpEstimate.Analysis
open scoped ContDiff

private theorem fullLogProfile_admissible (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M) :
    ContinuousOn (fun v => Real.log (M / D.a v)) (Icc (-1) 1) ∧
      ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ Real.log (M / D.a v) ∧
        Real.log (M / D.a v) ≤ Real.log (M / m) := by
  refine ⟨continuousOn_log_reciprocal D.a M (D.reciprocalCap_parameters m M hm hb).1
    _ D.a_contDiff.continuous.continuousOn D.a_pos, ?_⟩
  exact fun v hv => log_reciprocal_bounds m M (D.a v) hm (hb v hv).1 (hb v hv).2

/-- The actual hemisphere deficit is the original constant-zonal action with its
exact geometric normalization and the canonical optimal pair value. -/
theorem hemisphereDeficit_logProfile_eq_normalized_constant_zonal (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    hemisphereDeficit (M / m) (fun v => Real.log (M / D.a v)) =
      oneFormDissipation D.metric
        (D.meridionalOneForm (fun _ => c) contDiff_const +
          D.azimuthalOneForm (fun _ => d) contDiff_const) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m)) := by
  rw [D.oneFormDissipation_constant_zonal_eq_pair_sum M
    (D.reciprocalCap_parameters m M hm hb).1 c d]
  unfold hemisphereDeficit
  field_simp [Real.pi_ne_zero, hcd.ne']
  ring

/-- The normalized original action controls the full logarithm's distance from
the even extension of the canonical obstacle optimizer. -/
theorem oneFormDissipation_constant_zonal_controls_evenExtension (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) - obstacleLogProfile (M / m) |v|) ^ 2) ≤
      (oneFormDissipation D.metric
        (D.meridionalOneForm (fun _ => c) contDiff_const +
          D.azimuthalOneForm (fun _ => d) contDiff_const) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  obtain ⟨hh, hbox⟩ := fullLogProfile_admissible D m M hm hb
  have h := hemisphereDeficit_controls_evenExtension (M / m)
    (D.reciprocalCap_parameters m M hm hb).2 _ hh hbox
  rwa [D.hemisphereDeficit_logProfile_eq_normalized_constant_zonal m M hm hb c d hcd] at h

/-- The normalized original action controls equatorial reflection error with the
same factor four as the two-hemisphere stability theorem. -/
theorem oneFormDissipation_constant_zonal_controls_reflection (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) - Real.log (M / D.a (-v))) ^ 2) ≤
      4 * (oneFormDissipation D.metric
        (D.meridionalOneForm (fun _ => c) contDiff_const +
          D.azimuthalOneForm (fun _ => d) contDiff_const) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  obtain ⟨hh, hbox⟩ := fullLogProfile_admissible D m M hm hb
  have h := hemisphereDeficit_controls_reflection (M / m)
    (D.reciprocalCap_parameters m M hm hb).2 _ hh hbox
  rwa [D.hemisphereDeficit_logProfile_eq_normalized_constant_zonal m M hm hb c d hcd] at h

/-- The normalized original action controls the full logarithm's error from its
actual equatorial symmetrization. -/
theorem oneFormDissipation_constant_zonal_controls_symmetrization (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) -
        (Real.log (M / D.a v) + Real.log (M / D.a (-v))) / 2) ^ 2) ≤
      (oneFormDissipation D.metric
        (D.meridionalOneForm (fun _ => c) contDiff_const +
          D.azimuthalOneForm (fun _ => d) contDiff_const) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  obtain ⟨hh, hbox⟩ := fullLogProfile_admissible D m M hm hb
  have h := hemisphereDeficit_controls_symmetrization (M / m)
    (D.reciprocalCap_parameters m M hm hb).2 _ hh hbox
  rwa [D.hemisphereDeficit_logProfile_eq_normalized_constant_zonal m M hm hb c d hcd] at h

/-- A zero squared coefficient sum means both coefficients, the actual section,
and its original action vanish. No normalization or profile rigidity is asserted. -/
theorem constant_zonal_zero_of_sq_sum_eq_zero (D : PoleData) (c d : ℝ)
    (hcd : c ^ 2 + d ^ 2 = 0) :
    c = 0 ∧ d = 0 ∧
      D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const = 0 ∧
      oneFormDissipation D.metric
        (D.meridionalOneForm (fun _ => c) contDiff_const +
          D.azimuthalOneForm (fun _ => d) contDiff_const) = 0 := by
  have hc : c = 0 := by nlinarith [sq_nonneg d]
  have hd : d = 0 := by nlinarith [sq_nonneg c]
  refine ⟨hc, hd, ?_, ?_⟩
  · subst c d
    ext x slots
    simp
  · rw [D.oneFormDissipation_constant_zonal, hcd, mul_zero]

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
