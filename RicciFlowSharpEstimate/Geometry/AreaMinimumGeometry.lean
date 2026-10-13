/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaJointMinimum

/-!
# Original smooth geometric recovery of an actual joint minimum

The minimum is produced from the smooth problem. Recovery returns the same
curvatures, normalized probes, inverse coordinates, actual metric/form
producers and complete dissipation equations as the geometric realization.
No smooth minimum or continuous parameter family is assumed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology DifferentialGeometry.Geometry.Curvature
open scoped ContDiff ENNReal

/-- Every cap at least one has a recoverable weak minimum and actual original
smooth nonzero metric/form realizations approaching its action. All geometric
producer equations remain tied to the recovered smooth curvature and probe. -/
theorem exists_area_minimizer_with_geometric_recovery (C : ℝ) (hC : 1 ≤ C) :
    ∃ K0 r0 p0 z0 : ℝ → ℝ,
      IsRecoverableAreaCompetitor C K0 r0 p0 z0 ∧
      ContinuousOn r0 (Ioo (0 : ℝ) 1) ∧ ContinuousOn p0 (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r0 x ≠ 0) ∧
      weakMeridionalAction K0 r0 p0 z0 = smoothAreaInfimum C ∧
      (∀ K r p z : ℝ → ℝ, IsRecoverableAreaCompetitor C K r p z →
        weakMeridionalAction K0 r0 p0 z0 ≤ weakMeridionalAction K r p z) ∧
    ∃ (Ks rs : ℕ → ℝ → ℝ) (κs Λs : ℕ → ℝ),
      (∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n)) ∧
      Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
        (𝓝 (smoothAreaInfimum C)) ∧
    ∃ (N : ℕ) (α : ℕ → ℝ) (X : ℕ → ℝ → ℝ)
      (D : ℕ → RotationalProfile.PoleData) (R : ℕ → ℝ → ℝ)
      (hR : ∀ n, ContDiff ℝ ∞ (R n)),
      (∀ n, α n = 1 / Real.sqrt (probeMass (Ks (n + N)) (rs (n + N)))) ∧
      (∀ n, 0 < α n) ∧ Tendsto α atTop (𝓝 1) ∧
      (∀ n, ContDiff ℝ ∞ (fun x => α n * rs (n + N) x)) ∧
      (∀ n, probeMass (Ks (n + N)) (fun x => α n * rs (n + N) x) = 1) ∧
      (∀ n, ∃ x ∈ Ioo (0 : ℝ) 1, α n * rs (n + N) x ≠ 0) ∧
      (∀ n, meridionalAction (Ks (n + N)) (fun x => α n * rs (n + N) x) =
        α n ^ 2 * meridionalAction (Ks (n + N)) (rs (n + N))) ∧
      Tendsto (fun n => meridionalAction (Ks (n + N))
        (fun x => α n * rs (n + N) x)) atTop (𝓝 (smoothAreaInfimum C)) ∧
      (∀ n, 0 < κs (n + N) ∧ Λs (n + N) / κs (n + N) ≤ C ∧
        (∀ x ∈ Icc (0 : ℝ) 1, Ks (n + N) x ∈ Icc (κs (n + N)) (Λs (n + N))) ∧
        (∫ x in (0 : ℝ)..1, Ks (n + N) x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * Ks (n + N) x) = 1) ∧
      (∀ n, ContDiff ℝ ∞ (X n) ∧
        heightCoordinate (Ks (n + N)) 0 = -1 ∧ heightCoordinate (Ks (n + N)) 1 = 1 ∧
        X n (-1) = 0 ∧ X n 1 = 1 ∧
        MapsTo (heightCoordinate (Ks (n + N))) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
        MapsTo (X n) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          X n (heightCoordinate (Ks (n + N)) x) = x ∧
          (D n).a (heightCoordinate (Ks (n + N)) x) = 1 / Ks (n + N) x ∧
          R n (heightCoordinate (Ks (n + N)) x) = α n * rs (n + N) x ∧
          RotationalProfile.warp (D n).a (heightCoordinate (Ks (n + N)) x) =
            warp (Ks (n + N)) x) ∧
        (∀ v ∈ Icc (-1 : ℝ) 1,
          heightCoordinate (Ks (n + N)) (X n v) = v ∧
          deriv (X n) v * Ks (n + N) (X n v) = 1) ∧
        R n = (fun x => α n * rs (n + N) x) ∘ X n ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          deriv (D n).a (heightCoordinate (Ks (n + N)) x) =
            -deriv (Ks (n + N)) x / Ks (n + N) x ^ 3 ∧
          deriv (R n) (heightCoordinate (Ks (n + N)) x) =
            deriv (fun x => α n * rs (n + N) x) x / Ks (n + N) x ∧
          deriv (deriv (R n)) (heightCoordinate (Ks (n + N)) x) =
            deriv (deriv (fun x => α n * rs (n + N) x)) x / Ks (n + N) x ^ 2 -
              deriv (fun x => α n * rs (n + N) x) x * deriv (Ks (n + N)) x /
                Ks (n + N) x ^ 3) ∧
        (∀ p : RotationalSphere,
          metricScalarAt (D n).metric p / 2 = Ks (n + N) (X n (sphereHeight p))) ∧
        oneFormDissipation (D n).metric ((D n).meridionalOneForm (R n) (hR n)) =
          2 * Real.pi * meridionalAction (Ks (n + N)) (fun x => α n * rs (n + N) x)) ∧
      (∀ n, MapsTo (heightCoordinate (Ks (n + N))) (Ioo (0 : ℝ) 1) (Ioo (-1 : ℝ) 1)) ∧
      (∀ n, ∀ p : RotationalSphere,
        metricScalarAt (D n).metric p / 2 ∈ Icc (κs (n + N)) (Λs (n + N))) ∧
      (∀ n, (D n).meridionalOneForm (R n) (hR n) ≠ 0) ∧
      Tendsto (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (R n) (hR n))) atTop
        (𝓝 (2 * Real.pi * smoothAreaInfimum C)) := by
  classical
  obtain ⟨K0, r0, p0, z0, hRecoverable, hr0c, hp0c, hnz, hEq, hMin⟩ :=
    exists_recoverable_area_minimizer C hC
  obtain ⟨_, _, Ks, rs, hS, hAction⟩ := hRecoverable.exists_action_recovery hC
  choose κs Λs hκs hboxs hratios using fun n => (hS n).2.2.1
  have hAction' : Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
      (𝓝 (smoothAreaInfimum C)) := by simpa only [hEq] using hAction
  have hm : ∀ n, probeMass (Ks n) (rs n) = 1 := fun n => (hS n).2.2.2.2.2
  refine ⟨K0, r0, p0, z0, hRecoverable, hr0c, hp0c, hnz, hEq, hMin,
    Ks, rs, κs, Λs, hS, hAction', ?_⟩
  exact exists_smooth_geometric_recovery_of_scalar_limits Ks rs κs Λs C
    (smoothAreaInfimum C) (fun n => (hS n).1) (fun n => (hS n).2.1) hκs hboxs hratios
    (fun n => (hS n).2.2.2.1) (fun n => (hS n).2.2.2.2.1)
    (by simpa only [hm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))) hAction'

end RicciFlowSharpEstimate.Geometry.AreaProfile
