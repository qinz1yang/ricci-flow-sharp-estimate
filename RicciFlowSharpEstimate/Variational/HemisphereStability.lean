/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.Stability
import RicciFlowSharpEstimate.Analysis.ReflectionEnergy

/-!
# Two-hemisphere stability and equatorial symmetry

The two actual hemisphere deficits control distance to the even extension of
the canonical optimizer, reflection error, and symmetrization error. Reflection
symmetry and geometric balance are not hypotheses.
-/

open Set

namespace RicciFlowSharpEstimate.Variational

/-- The sum of the actual northern and southern pair deficits. -/
noncomputable def hemisphereDeficit (C : ℝ) (h : ℝ → ℝ) : ℝ :=
  pairFunctional h + pairFunctional (fun v => h (-v)) -
    2 * pairFunctional (obstacleLogProfile C)

private theorem hemisphere_error_budget (C : ℝ) (hC : 1 ≤ C)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1) 1))
    (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ h v ∧ h v ≤ Real.log C) :
    stabilityConstant C *
      ((∫ v in (0 : ℝ)..1, (h v - obstacleLogProfile C v) ^ 2) +
        (∫ v in (0 : ℝ)..1, (h (-v) - obstacleLogProfile C v) ^ 2)) ≤
      hemisphereDeficit C h := by
  have hi (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : v ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hv.1], hv.2⟩
  have hn (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : -v ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  have hplus := pairFunctional_deficit_controls_L2 C hC h (hh.mono hi)
    (fun v hv => hbox v (hi v hv))
  have hminus := pairFunctional_deficit_controls_L2 C hC (fun v => h (-v))
    (hh.comp continuous_neg.continuousOn hn) (fun v hv => hbox (-v) (hn v hv))
  dsimp [hemisphereDeficit]
  linarith

/-- Small hemisphere deficits force the full profile close to the even optimizer. -/
theorem hemisphereDeficit_controls_evenExtension (C : ℝ) (hC : 1 ≤ C)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1) 1))
    (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ h v ∧ h v ≤ Real.log C) :
    (∫ v in (-1 : ℝ)..1, (h v - obstacleLogProfile C |v|) ^ 2) ≤
      hemisphereDeficit C h / stabilityConstant C := by
  rw [Analysis.integral_evenExtension_error_sq_eq h (obstacleLogProfile C) hh
    (continuous_obstacleLogProfile C).continuousOn]
  apply (le_div_iff₀ (stabilityConstant_pos C hC)).2
  simpa only [mul_comm] using hemisphere_error_budget C hC h hh hbox

/-- Near-equatorial symmetry follows from the deficits, without a reflection hypothesis. -/
theorem hemisphereDeficit_controls_reflection (C : ℝ) (hC : 1 ≤ C)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1) 1))
    (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ h v ∧ h v ≤ Real.log C) :
    (∫ v in (-1 : ℝ)..1, (h v - h (-v)) ^ 2) ≤
      4 * hemisphereDeficit C h / stabilityConstant C := by
  have hr := Analysis.integral_reflection_error_sq_le h (obstacleLogProfile C) hh
    (continuous_obstacleLogProfile C).continuousOn
  have hp := mul_le_mul_of_nonneg_left hr (stabilityConstant_pos C hC).le
  have hb := hemisphere_error_budget C hC h hh hbox
  apply (le_div_iff₀ (stabilityConstant_pos C hC)).2
  nlinarith only [hp, hb]

/-- The actual equatorial symmetrization has squared error at most the deficit divided by c(C). -/
theorem hemisphereDeficit_controls_symmetrization (C : ℝ) (hC : 1 ≤ C)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1) 1))
    (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ h v ∧ h v ≤ Real.log C) :
    (∫ v in (-1 : ℝ)..1, (h v - (h v + h (-v)) / 2) ^ 2) ≤
      hemisphereDeficit C h / stabilityConstant C := by
  rw [Analysis.integral_symmetrization_error_sq_eq]
  have hr := hemisphereDeficit_controls_reflection C hC h hh hbox
  convert mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 1 / 4) using 1
  ring

end RicciFlowSharpEstimate.Variational
