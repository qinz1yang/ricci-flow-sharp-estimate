/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.MeridionalAction
import RicciFlowSharpEstimate.Variational.ReciprocalProfile

/-!
# The actual hemisphere pair functionals

The northern and southern reciprocal logarithms of the original pole-data
profile give the two meridional-weight integrals. The southern identity follows
from the actual balance law, without an equatorial symmetry hypothesis. All
regularity and obstacle bounds are derived from the original physical profile.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set MeasureTheory Variational RicciFlowSharpEstimate.Analysis
open scoped ContDiff

private theorem north_mem_physical {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    v ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩

private theorem south_mem_physical {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    -v ∈ Icc (-1 : ℝ) 1 := by
  constructor <;> linarith [hv.1, hv.2]

/-- The literal northern logarithm is continuous through the equator and pole. -/
theorem northLogProfile_continuousOn (D : PoleData) (M : ℝ) (hM : 0 < M) :
    ContinuousOn (fun v => Real.log (M / D.a v)) (Icc 0 1) :=
  continuousOn_log_reciprocal D.a M hM _ D.a_contDiff.continuous.continuousOn
    (fun _ hv => D.a_pos _ (north_mem_physical hv))

/-- The literal southern logarithm is continuous through the equator and pole. -/
theorem southLogProfile_continuousOn (D : PoleData) (M : ℝ) (hM : 0 < M) :
    ContinuousOn (fun v => Real.log (M / D.a (-v))) (Icc 0 1) :=
  continuousOn_log_reciprocal _ M hM _
    (D.a_contDiff.continuous.comp continuous_neg).continuousOn
    (fun _ hv => D.a_pos _ (south_mem_physical hv))

/-- The northern logarithm has the exact reciprocal-profile derivative. -/
theorem northLogProfile_hasDerivAt (D : PoleData) (M : ℝ) (hM : 0 < M)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun x => Real.log (M / D.a x)) (-deriv D.a v / D.a v) v :=
  hasDerivAt_log_reciprocal D.a M v _ hM
    (D.a_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    (D.a_pos v (north_mem_physical hv))

/-- Reflection reverses the sign in the southern logarithmic derivative. -/
theorem southLogProfile_hasDerivAt (D : PoleData) (M : ℝ) (hM : 0 < M)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun x => Real.log (M / D.a (-x)))
      (deriv D.a (-v) / D.a (-v)) v := by
  have ha : HasDerivAt (fun x => D.a (-x)) (-deriv D.a (-v)) v := by
    simpa only [Function.comp_def, mul_neg_one] using!
      ((D.a_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt.comp v
        (hasDerivAt_neg v))
  simpa only [neg_neg] using hasDerivAt_log_reciprocal (fun x => D.a (-x)) M v _ hM ha
    (D.a_pos (-v) (south_mem_physical hv))

/-- The northern logarithm is differentiable on the open physical hemisphere. -/
theorem northLogProfile_differentiableOn (D : PoleData) (M : ℝ) (hM : 0 < M) :
    DifferentiableOn ℝ (fun v => Real.log (M / D.a v)) (Ioo 0 1) :=
  fun v hv =>
    (D.northLogProfile_hasDerivAt M hM v ⟨hv.1.le, hv.2.le⟩).differentiableAt.differentiableWithinAt

/-- The southern logarithm is differentiable on the open physical hemisphere. -/
theorem southLogProfile_differentiableOn (D : PoleData) (M : ℝ) (hM : 0 < M) :
    DifferentiableOn ℝ (fun v => Real.log (M / D.a (-v))) (Ioo 0 1) :=
  fun v hv =>
    (D.southLogProfile_hasDerivAt M hM v ⟨hv.1.le, hv.2.le⟩).differentiableAt.differentiableWithinAt

/-- Natural bounds on the physical profile imply a positive normalization and admissible cap. -/
theorem reciprocalCap_parameters (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M) :
    0 < M ∧ 1 ≤ M / m := by
  have hzero := hb 0 (by constructor <;> norm_num)
  have hmM := hzero.1.trans hzero.2
  exact ⟨hm.trans_le hmM, (le_div_iff₀ hm).2 (by simpa using hmM)⟩

/-- The literal northern logarithm obeys both obstacles from the actual profile bounds. -/
theorem northLogProfile_admissible (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M) :
    ContinuousOn (fun v => Real.log (M / D.a v)) (Icc 0 1) ∧
      ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ Real.log (M / D.a v) ∧
        Real.log (M / D.a v) ≤ Real.log (M / m) := by
  refine ⟨D.northLogProfile_continuousOn M (D.reciprocalCap_parameters m M hm hb).1, ?_⟩
  intro v hv
  exact log_reciprocal_bounds m M (D.a v) hm
    (hb v (north_mem_physical hv)).1 (hb v (north_mem_physical hv)).2

/-- The literal southern logarithm obeys the same obstacles without symmetry. -/
theorem southLogProfile_admissible (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M) :
    ContinuousOn (fun v => Real.log (M / D.a (-v))) (Icc 0 1) ∧
      ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ Real.log (M / D.a (-v)) ∧
        Real.log (M / D.a (-v)) ≤ Real.log (M / m) := by
  refine ⟨D.southLogProfile_continuousOn M (D.reciprocalCap_parameters m M hm hb).1, ?_⟩
  intro v hv
  exact log_reciprocal_bounds m M (D.a (-v)) hm
    (hb (-v) (south_mem_physical hv)).1 (hb (-v) (south_mem_physical hv)).2

/-- Balance converts the reflected forward tail into the original southern warping coefficient. -/
theorem warp_reflected (D : PoleData) (v : ℝ) :
    warp (fun s => D.a (-s)) v = warp D.a (-v) := by
  have hchange : (∫ s in v..1, s * D.a (-s)) =
      -(∫ s in (-1 : ℝ)..(-v), s * D.a s) := by
    have hn := intervalIntegral.integral_comp_neg (fun s => s * D.a s) (a := v) (b := 1)
    simp only [neg_mul, intervalIntegral.integral_neg] at hn
    linarith
  rw [warp, warp, hchange,
    integral_from_eq_neg_integral_to_of_balance D.a D.a_contDiff.continuous D.balance_eq]

/-- The actual northern pair functional is exactly the northern meridional-weight integral. -/
theorem pairFunctional_northLogProfile (D : PoleData) (M : ℝ) (hM : 0 < M) :
    pairFunctional (fun v => Real.log (M / D.a v)) =
      ∫ v in 0..1, D.meridionalWeight v := by
  exact pairFunctional_log_reciprocal D.a M hM D.a_contDiff.continuous.continuousOn
    (fun _ hv => D.a_pos _ (north_mem_physical hv))

/-- The actual southern pair functional is exactly the original southern weight integral. -/
theorem pairFunctional_southLogProfile (D : PoleData) (M : ℝ) (hM : 0 < M) :
    pairFunctional (fun v => Real.log (M / D.a (-v))) =
      ∫ v in 0..1, D.meridionalWeight (-v) := by
  rw [pairFunctional_log_reciprocal (fun v => D.a (-v)) M hM
    (D.a_contDiff.continuous.comp continuous_neg).continuousOn
    (fun _ hv => D.a_pos _ (south_mem_physical hv))]
  apply intervalIntegral.integral_congr
  intro v _
  change warp (fun s => D.a (-s)) v / D.a (-v) = warp D.a (-v) / D.a (-v)
  rw [D.warp_reflected]

/-- Both actual hemisphere pair integrals sum to the full meridional-weight integral. -/
theorem integral_meridionalWeight_eq_pairFunctional_sum (D : PoleData) (M : ℝ)
    (hM : 0 < M) :
    (∫ v in (-1 : ℝ)..1, D.meridionalWeight v) =
      pairFunctional (fun v => Real.log (M / D.a v)) +
        pairFunctional (fun v => Real.log (M / D.a (-v))) := by
  have hl : IntervalIntegrable D.meridionalWeight volume (-1) 0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact D.meridionalWeight_continuousOn.mono
      (fun _ hv => ⟨hv.1, hv.2.trans zero_le_one⟩)
  have hr : IntervalIntegrable D.meridionalWeight volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact D.meridionalWeight_continuousOn.mono (fun _ hv => north_mem_physical hv)
  have hn : (∫ v in (0 : ℝ)..1, D.meridionalWeight (-v)) =
      ∫ v in (-1 : ℝ)..0, D.meridionalWeight v := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg D.meridionalWeight (a := 0) (b := 1))
  rw [D.pairFunctional_northLogProfile M hM, D.pairFunctional_southLogProfile M hM,
    hn, add_comm]
  exact (intervalIntegral.integral_add_adjacent_intervals hl hr).symm

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
