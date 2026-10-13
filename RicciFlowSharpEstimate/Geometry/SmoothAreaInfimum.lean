/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionCoercivity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic.Choose

/-!
# The infimum over the actual smooth normalized area class

The competitors retain the original positive curvature-ratio restriction,
the two exact curvature moments, and unit mass of the actual smooth probe.
Coercivity gives a finite common lower bound. The round competitor gives
action four, so a tail of an infimizing sequence has action at most five.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped ContDiff Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The original smooth curvature-ratio class with exact moments and unit probe mass. -/
def IsSmoothAreaCompetitor (C : ℝ) (K r : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ r ∧
    (∃ κ Λ : ℝ, 0 < κ ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C) ∧
    (∫ x in (0 : ℝ)..1, K x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧ probeMass K r = 1

/-- The complete action values of the actual smooth normalized competitors. -/
def smoothAreaActionValues (C : ℝ) : Set ℝ :=
  {a | ∃ K r, IsSmoothAreaCompetitor C K r ∧ meridionalAction K r = a}

/-- The infimum of the complete action over the original smooth class. -/
def smoothAreaInfimum (C : ℝ) : ℝ := sInf (smoothAreaActionValues C)

/-- The original ratio and normalized moment give a common curvature box. -/
theorem IsSmoothAreaCompetitor.common_bounds {C : ℝ} {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor C K r) :
    ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ K x ∧ K x ≤ 2 * C := by
  rcases h with ⟨hK, _, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, _, _⟩
  exact curvature_bounds_of_ratio K hK.continuous κ Λ C hκ hbox hratio hzero

/-- The actual curvature belongs to L² on the area interval by its original box. -/
theorem IsSmoothAreaCompetitor.memLp_curvature {C : ℝ} {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor C K r) : MemLp K 2 areaμ := by
  rcases h with ⟨hK, _, ⟨κ, Λ, hκ, hbox, _⟩, _, _, _⟩
  apply MemLp.of_bound hK.continuous.aestronglyMeasurable Λ
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := hbox x ⟨hx.1.le, hx.2.le⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans hb.1)] using hb.2

/-- The constant round probe of size `sqrt 3` has unit physical weighted mass. -/
theorem probeMass_two_sqrt_three :
    probeMass (fun _ => 2) (fun _ => Real.sqrt 3) = 1 := by
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hi1 : IntervalIntegrable (fun x : ℝ => 2 * x) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x : ℝ => 2 * x ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  unfold probeMass
  simp only [warp_two, hsqrt]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_const_mul (2 : ℝ) (fun x => x)]
  norm_num [intervalIntegral.integral_const_mul, integral_pow, integral_id]

/-- The same normalized round probe has complete action four. -/
theorem meridionalAction_two_sqrt_three :
    meridionalAction (fun _ => 2) (fun _ => Real.sqrt 3) = 4 := by
  have hzero : (∫ _x in (0 : ℝ)..1, (2 : ℝ)) = 2 := by norm_num
  have hone : (∫ x in (0 : ℝ)..1, x * (2 : ℝ)) = 1 := by
    norm_num [intervalIntegral.integral_mul_const, integral_id]
  have hscale := meridionalAction_const_mul (fun _ => 2) (fun _ => 1)
    contDiff_const contDiff_const hzero hone (Real.sqrt 3)
  calc
    meridionalAction (fun _ => 2) (fun _ => Real.sqrt 3) =
        Real.sqrt (3 : ℝ) ^ 2 * (4 / 3) := by
      simpa only [mul_one, meridionalAction_two_one] using hscale
    _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

/-- The normalized round pair belongs to every smooth class with ratio bound at least one. -/
theorem isSmoothAreaCompetitor_round (C : ℝ) (hC : 1 ≤ C) :
    IsSmoothAreaCompetitor C (fun _ => 2) (fun _ => Real.sqrt 3) := by
  refine ⟨contDiff_const, contDiff_const, ?_, ?_, ?_, probeMass_two_sqrt_three⟩
  · refine ⟨2, 2, by norm_num, ?_, ?_⟩
    · intro x _
      norm_num
    · simpa using hC
  · norm_num
  · norm_num [intervalIntegral.integral_mul_const, integral_id]

/-- Coercivity gives one finite lower bound for the entire original smooth ratio class. -/
theorem IsSmoothAreaCompetitor.action_lower_bound {C : ℝ} {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor C K r) (hC : 1 ≤ C) :
    -actionMassCorrection (2 / C) (2 * C) ≤ meridionalAction K r := by
  rcases h with ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, hmass⟩
  have hcoercive := meridionalAction_coercive_of_curvature_ratio K r hK.continuous
    (hr.of_le (by simp)) κ Λ C hκ hC hbox hratio hzero hone
  rw [hmass, mul_one] at hcoercive
  have hE := probeOperatorEnergy_nonneg K r hK.continuous
    (fun x hx => hκ.le.trans (hbox x hx).1) hzero hone
  have hU : 0 ≤ ∫ x in (0 : ℝ)..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (r x))
  linarith only [hcoercive, hE, hU]

/-- The smooth action-value set is nonempty, witnessed by the normalized round pair. -/
theorem smoothAreaActionValues_nonempty (C : ℝ) (hC : 1 ≤ C) :
    (smoothAreaActionValues C).Nonempty := by
  exact ⟨4, (fun _ => 2), (fun _ => Real.sqrt 3),
    isSmoothAreaCompetitor_round C hC, meridionalAction_two_sqrt_three⟩

/-- All smooth action values have the same finite coercive lower bound. -/
theorem smoothAreaActionValues_bddBelow (C : ℝ) (hC : 1 ≤ C) :
    BddBelow (smoothAreaActionValues C) := by
  refine ⟨-actionMassCorrection (2 / C) (2 * C), ?_⟩
  rintro a ⟨K, r, h, rfl⟩
  exact h.action_lower_bound hC

/-- The smooth infimum is a lower bound for the action of each actual competitor. -/
theorem smoothAreaInfimum_le_action (C : ℝ) (hC : 1 ≤ C) (K r : ℝ → ℝ)
    (h : IsSmoothAreaCompetitor C K r) :
    smoothAreaInfimum C ≤ meridionalAction K r := by
  exact csInf_le (smoothAreaActionValues_bddBelow C hC) ⟨K, r, h, rfl⟩

/-- The normalized round pair gives the common upper bound four for the smooth infimum. -/
theorem smoothAreaInfimum_le_four (C : ℝ) (hC : 1 ≤ C) :
    smoothAreaInfimum C ≤ 4 := by
  simpa only [meridionalAction_two_sqrt_three] using
    smoothAreaInfimum_le_action C hC (fun _ => 2) (fun _ => Real.sqrt 3)
      (isSmoothAreaCompetitor_round C hC)

/-- The smooth infimum retains the explicit finite coercive lower bound. -/
theorem neg_actionMassCorrection_le_smoothAreaInfimum (C : ℝ) (hC : 1 ≤ C) :
    -actionMassCorrection (2 / C) (2 * C) ≤ smoothAreaInfimum C := by
  apply le_csInf (smoothAreaActionValues_nonempty C hC)
  rintro a ⟨K, r, h, rfl⟩
  exact h.action_lower_bound hC

/-- There is a sequence of actual smooth normalized competitors approaching the
smooth infimum, all in the common complete-action sublevel five. -/
theorem exists_smooth_area_minimizing_sequence (C : ℝ) (hC : 1 ≤ C) :
    ∃ K r : ℕ → ℝ → ℝ,
      (∀ n, IsSmoothAreaCompetitor C (K n) (r n)) ∧
      (∀ n, meridionalAction (K n) (r n) ≤ 5) ∧
      Tendsto (fun n => meridionalAction (K n) (r n)) atTop
        (nhds (smoothAreaInfimum C)) := by
  classical
  obtain ⟨u, _, hu, hmem⟩ := exists_seq_tendsto_sInf
    (smoothAreaActionValues_nonempty C hC) (smoothAreaActionValues_bddBelow C hC)
  have hlimit : Tendsto u atTop (nhds (smoothAreaInfimum C)) := hu
  have hwitness (n : ℕ) :
      ∃ K r, IsSmoothAreaCompetitor C K r ∧ meridionalAction K r = u n := hmem n
  choose K r hcomp haction using hwitness
  have hlt : smoothAreaInfimum C < 5 :=
    (smoothAreaInfimum_le_four C hC).trans_lt (by norm_num)
  have heventually : ∀ᶠ n in atTop, u n < 5 :=
    hlimit.eventually (gt_mem_nhds hlt)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨fun n => K (n + N), fun n => r (n + N),
    fun n => hcomp (n + N), ?_, ?_⟩
  · intro n
    rw [haction]
    exact (hN (n + N) (Nat.le_add_left N n)).le
  · have hshift := hlimit.comp (tendsto_add_atTop_nat N)
    simpa only [Function.comp_def, haction] using hshift

end RicciFlowSharpEstimate.Geometry.AreaProfile
