/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothReciprocalRecovery
import RicciFlowSharpEstimate.Geometry.ConformalKillingSafety

/-!
# Smooth conformal-Killing witnesses and critical recovery

The same fixed unit meridional probe has negative action below every prescribed
supercritical cap. At the critical cap its smooth recovery actions are positive
and converge to zero, with no rescaling of the scalar probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open Set Filter Variational DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Topology

/-- Every larger cap contains a smooth even produced metric whose original
nonzero unit CK meridional form has negative complete action. The profile and
actual curvature are tied to the same metric, with a strictly intermediate cap. -/
theorem exists_negative_unit_meridional_of_criticalCap_lt (C : ℝ)
    (hC : criticalCap < C) :
    let C₀ := (C + criticalCap) / 2
    ∃ a : ℝ → ℝ, ∃ D : PoleData,
      D.a = a ∧ ContDiff ℝ ∞ a ∧ Function.Even a ∧
      (∀ v, 1 / C₀ ≤ a v ∧ a v ≤ 1) ∧ balance a = 0 ∧
      D.meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 ∧
      IsConformalKillingOneForm D.metric
        (D.meridionalOneForm (fun _ => 1) contDiff_const) ∧
      (∀ x : RotationalSphere, 1 ≤ metricScalarAt D.metric x / 2 ∧
        metricScalarAt D.metric x / 2 ≤ C₀) ∧
      C₀ < C ∧
      oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) < 0 := by
  dsimp only
  let C₀ := (C + criticalCap) / 2
  have hmid : criticalCap < C₀ := by dsimp [C₀]; linarith
  have hmidC : C₀ < C := by dsimp [C₀]; linarith
  have hmid1 : 1 ≤ C₀ := (one_lt_criticalCap.trans hmid).le
  have hmidpos : 0 < C₀ := zero_lt_one.trans_le hmid1
  obtain ⟨A, D, hA, _, hlim⟩ := exists_poleData_unit_probe_recovery C₀ hmid1
  have hval : pairFunctional (obstacleLogProfile C₀) < 1 / 3 := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hmid)
      ((pairFunctional_obstacleLogProfile_ge_one_third_iff C₀ hmid1).mp h)
  have hneg : 8 * Real.pi * (pairFunctional (obstacleLogProfile C₀) - 1 / 3) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hval)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hneg)).exists
  obtain ⟨hDa, hsmooth, heven, hbox, hbalance⟩ := hA n
  refine ⟨A n, D n, hDa, hsmooth, heven, hbox, hbalance,
    (D n).meridionalOneForm_one_ne_zero,
    (D n).isConformalKillingOneForm_meridional_const 1, ?_, hmidC, hn⟩
  apply ((D n).curvature_bounds_iff_profile_bounds 1 C₀ zero_lt_one hmidpos).mpr
  intro v _
  simpa only [hDa, div_one] using hbox v

/-- At the critical cap, one sequence of genuine smooth metrics recovers zero
action with the fixed unit probe, while every member has strictly positive
action. The approximants, producer equations, curvature box and nonzero CK
sections are all retained in the conclusion. -/
theorem exists_critical_unit_probe_recovery :
    ∃ A : ℕ → ℝ → ℝ, ∃ D : ℕ → PoleData,
      (∀ n, (D n).a = A n ∧ ContDiff ℝ ∞ (A n) ∧ Function.Even (A n) ∧
        (∀ v, 1 / criticalCap ≤ A n v ∧ A n v ≤ 1) ∧ balance (A n) = 0 ∧
        (D n).meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 ∧
        IsConformalKillingOneForm (D n).metric
          ((D n).meridionalOneForm (fun _ => 1) contDiff_const) ∧
        (∀ x : RotationalSphere, 1 ≤ metricScalarAt (D n).metric x / 2 ∧
          metricScalarAt (D n).metric x / 2 ≤ criticalCap) ∧
        0 < oneFormDissipation (D n).metric
          ((D n).meridionalOneForm (fun _ => 1) contDiff_const)) ∧
      TendstoUniformly A (evenReciprocalProfile criticalCap) atTop ∧
      Tendsto (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (fun _ => 1) contDiff_const)) atTop (𝓝 0) := by
  obtain ⟨A, D, hA, hlim, hQ⟩ :=
    exists_poleData_unit_probe_recovery criticalCap one_lt_criticalCap.le
  rw [pairFunctional_obstacleLogProfile_criticalCap, sub_self, mul_zero] at hQ
  refine ⟨A, D, ?_, hlim, hQ⟩
  intro n
  obtain ⟨hDa, hsmooth, heven, hbox, hbalance⟩ := hA n
  refine ⟨hDa, hsmooth, heven, hbox, hbalance,
    (D n).meridionalOneForm_one_ne_zero,
    (D n).isConformalKillingOneForm_meridional_const 1, ?_, ?_⟩
  · apply ((D n).curvature_bounds_iff_profile_bounds 1 criticalCap zero_lt_one
      (zero_lt_one.trans one_lt_criticalCap)).mpr
    intro v _
    simpa only [hDa, div_one] using hbox v
  · apply (D n).oneFormDissipation_meridional_one_pos_of_profile_bounds
      (1 / criticalCap) 1 (one_div_pos.mpr (zero_lt_one.trans one_lt_criticalCap))
    · intro v _
      simpa only [hDa] using hbox v
    · simp only [one_div_one_div, le_refl]

end RicciFlowSharpEstimate.Geometry.RotationalProfile
