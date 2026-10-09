/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.EvenSmoothApproximation
import RicciFlowSharpEstimate.Geometry.ReciprocalProfileAction
import RicciFlowSharpEstimate.Geometry.ConstantProbeContinuity
import RicciFlowSharpEstimate.Geometry.ConstantZonalAction

/-!
# Smooth recovery of the reciprocal optimizer

Even convolution approximants preserve the exact box and balance. Each is
realized by the existing smooth metric producer, and the original unit
meridional action converges to the actual relaxed variational value.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open Set Filter MeasureTheory Variational
open scoped ContDiff Topology

/-- Globally smooth even approximants preserve the reciprocal box, exact balance,
and uniform convergence to the actual clamped reciprocal optimizer. -/
theorem exists_smooth_even_reciprocal_profiles (C : ℝ) (hC : 1 ≤ C) :
    ∃ A : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (A n) ∧ Function.Even (A n) ∧
        (∀ v, 1 / C ≤ A n v ∧ A n v ≤ 1) ∧ balance (A n) = 0) ∧
      TendstoUniformly A (evenReciprocalProfile C) atTop := by
  obtain ⟨A, hA, hlim⟩ := Analysis.exists_contDiff_even_sequence_Icc
    (uniformContinuous_evenReciprocalProfile C) (even_evenReciprocalProfile C)
    (evenReciprocalProfile_bounds C hC)
  exact ⟨A, fun n => ⟨(hA n).1, (hA n).2.1, (hA n).2.2,
    balance_eq_zero_of_even _ (hA n).2.1⟩, hlim⟩

/-- The original unit meridional action equals its derivative-free profile integral. -/
theorem PoleData.oneFormDissipation_meridional_one_eq_integral (D : PoleData) :
    oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) =
      2 * Real.pi * (2 * (∫ v in (-1 : ℝ)..1, warp D.a v / D.a v) - 4 / 3) := by
  rw [D.oneFormDissipation_meridional, D.meridionalAction_const]
  simp only [one_pow, mul_one, PoleData.meridionalWeight]

/-- Smooth reciprocal recovery produces genuine pole data tied to each approximant
and convergence of the original complete action with the fixed scalar probe one. -/
theorem exists_poleData_unit_probe_recovery (C : ℝ) (hC : 1 ≤ C) :
    ∃ A : ℕ → ℝ → ℝ, ∃ D : ℕ → PoleData,
      (∀ n, (D n).a = A n ∧ ContDiff ℝ ∞ (A n) ∧ Function.Even (A n) ∧
        (∀ v, 1 / C ≤ A n v ∧ A n v ≤ 1) ∧ balance (A n) = 0) ∧
      TendstoUniformly A (evenReciprocalProfile C) atTop ∧
      Tendsto (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (fun _ => 1) contDiff_const))
        atTop (𝓝 (8 * Real.pi * (pairFunctional (obstacleLogProfile C) - 1 / 3))) := by
  obtain ⟨A, hA, hlim⟩ := exists_smooth_even_reciprocal_profiles C hC
  have hlo : 0 < 1 / C := one_div_pos.mpr (zero_lt_one.trans_le hC)
  have hex (n : ℕ) : ∃ D : PoleData, D.a = A n := by
    obtain ⟨D, hD, _⟩ := exists_poleData (A n) (hA n).1
      (fun v _ => hlo.trans_le ((hA n).2.2.1 v).1) (hA n).2.2.2
    exact ⟨D, hD⟩
  choose D hD using hex
  refine ⟨A, D, fun n => ⟨hD n, hA n⟩, hlim, ?_⟩
  have hint := tendsto_integral_warp_div_of_tendstoUniformlyOn hlo
    (fun n => (hA n).1.continuous.continuousOn)
    (fun n v _ => (hA n).2.2.1 v) hlim.tendstoUniformlyOn
  have hscalar := ((hint.const_mul 2).sub_const (4 / 3)).const_mul (2 * Real.pi)
  rw [constantProbeIntegral_evenReciprocalProfile C hC] at hscalar
  apply hscalar.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [(D n).oneFormDissipation_meridional_one_eq_integral, hD n]

end RicciFlowSharpEstimate.Geometry.RotationalProfile
