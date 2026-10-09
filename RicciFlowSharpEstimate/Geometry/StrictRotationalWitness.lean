/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothNegativeAreaRecovery
import RicciFlowSharpEstimate.Geometry.AreaGeometricRealization
import RicciFlowSharpEstimate.Geometry.ConformalKillingThreshold

/-!
# A smooth negative rotational witness below the CK threshold

The recovered exact-moment curvature and the same fixed plateau probe enter
the accepted smooth realizer. Its original metric, section, coordinate maps
and all tying equations remain visible in the negative witness.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature CriticalAreaProfile
open scoped Manifold ContDiff Topology

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The actual contracted recovery produces a smooth original-metric negative
witness with all physical maps, probe jets and action equations retained. -/
theorem exists_smooth_negative_geometric_realization :
    ∃ (r : ℝ → ℝ) (t : ℝ) (K X : ℝ → ℝ) (D : RotationalProfile.PoleData)
      (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R),
      ContDiff ℝ ∞ r ∧ r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧ 0 < t ∧ t < 1 ∧
      0 < contractedLower t ∧
      contractedUpper t / contractedLower t < conformalKillingThreshold ∧
      ContDiff ℝ ∞ K ∧
      (∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc (contractedLower t) (contractedUpper t)) ∧
      (∫ x in (0 : ℝ)..1, K x) = 2 ∧ (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x) ∧
      MonotoneOn K (Icc (1 / 2 : ℝ) 1) ∧ AntitoneOn K (Icc (0 : ℝ) (1 / 2)) ∧
      ContDiff ℝ ∞ X ∧
      AreaProfile.heightCoordinate K 0 = -1 ∧ AreaProfile.heightCoordinate K 1 = 1 ∧
      X (-1) = 0 ∧ X 1 = 1 ∧
      MapsTo (AreaProfile.heightCoordinate K) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
      MapsTo X (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        X (AreaProfile.heightCoordinate K x) = x ∧
        D.a (AreaProfile.heightCoordinate K x) = 1 / K x ∧
        R (AreaProfile.heightCoordinate K x) = r x ∧
        RotationalProfile.warp D.a (AreaProfile.heightCoordinate K x) = AreaProfile.warp K x) ∧
      (∀ v ∈ Icc (-1 : ℝ) 1,
        AreaProfile.heightCoordinate K (X v) = v ∧ deriv X v * K (X v) = 1) ∧
      R = r ∘ X ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        deriv D.a (AreaProfile.heightCoordinate K x) = -deriv K x / K x ^ 3 ∧
        deriv R (AreaProfile.heightCoordinate K x) = deriv r x / K x ∧
        deriv (deriv R) (AreaProfile.heightCoordinate K x) =
          deriv (deriv r) x / K x ^ 2 - deriv r x * deriv K x / K x ^ 3) ∧
      (∀ p : RotationalSphere,
        metricScalarAt D.metric p / 2 = K (X (sphereHeight p))) ∧
      oneFormDissipation D.metric (D.meridionalOneForm R hR) =
        2 * Real.pi * AreaProfile.meridionalAction K r ∧
      IsRepresentedRotationalMetric D.metric ∧
      (∀ p : RotationalSphere, contractedLower t ≤ metricScalarAt D.metric p / 2 ∧
        metricScalarAt D.metric p / 2 ≤ contractedUpper t) ∧
      D.meridionalOneForm R hR ≠ 0 ∧
      oneFormDissipation D.metric (D.meridionalOneForm R hR) < 0 := by
  obtain ⟨r, t, K, hr, hr0, hrd0, hn0, hn1, hnonconstant, ht0, ht1,
    hlo, hratio, hK, hbox, hzero, hone, hsymm, hmono, hanti, hnegArea⟩ :=
    CriticalAreaProfile.exists_smooth_negative_area_data
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < K x :=
    hlo.trans_le (hbox x hx).1
  obtain ⟨X, D, R, hR, hX, hV0, hV1, hX0, hX1, hVmap, hXmap,
    hforward, hbackward, hcomp, hjets, hcurv, haction⟩ :=
    AreaProfile.exists_smooth_geometric_realization K r hK hr hpos hzero hone
  have hneg : oneFormDissipation D.metric (D.meridionalOneForm R hR) < 0 := by
    rw [haction]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hnegArea
  have hnonzero : D.meridionalOneForm R hR ≠ 0 := by
    intro hz
    have h := hneg
    rw [hz, oneFormDissipation_zero] at h
    exact (lt_irrefl 0) h
  have hgeobox (p : RotationalSphere) :
      contractedLower t ≤ metricScalarAt D.metric p / 2 ∧
        metricScalarAt D.metric p / 2 ≤ contractedUpper t := by
    rw [hcurv]
    exact hbox _ (hXmap (sphereHeight_mem_Icc p))
  have hratioCK : contractedUpper t / contractedLower t < conformalKillingThreshold := by
    rw [conformalKillingThreshold_eq_criticalCap]
    exact hratio
  exact ⟨r, t, K, X, D, R, hR, hr, hr0, hrd0, hn0, hn1, hnonconstant,
    ht0, ht1, hlo, hratioCK, hK, hbox, hzero, hone, hsymm, hmono, hanti,
    hX, hV0, hV1, hX0, hX1, hVmap, hXmap, hforward, hbackward, hcomp, hjets,
    hcurv, haction, D.isRepresentedRotationalMetric, hgeobox, hnonzero, hneg⟩

/-- A genuine smooth original meridional form has negative dissipation in a
represented metric with a positive curvature box strictly below the CK threshold. -/
theorem exists_negative_rotational_below_conformalKillingThreshold :
    ∃ (t : ℝ) (D : RotationalProfile.PoleData) (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R),
      0 < t ∧ t < 1 ∧ 0 < contractedLower t ∧
      IsRepresentedRotationalMetric D.metric ∧
      (∀ p : RotationalSphere, contractedLower t ≤ metricScalarAt D.metric p / 2 ∧
        metricScalarAt D.metric p / 2 ≤ contractedUpper t) ∧
      D.meridionalOneForm R hR ≠ 0 ∧
      oneFormDissipation D.metric (D.meridionalOneForm R hR) < 0 ∧
      contractedUpper t / contractedLower t < conformalKillingThreshold := by
  obtain ⟨r, t, K, X, D, R, hR, _, _, _, _, _, _, ht0, ht1, hlo, hratio,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hrep, hbox, hnonzero, hneg⟩ := exists_smooth_negative_geometric_realization
  exact ⟨t, D, R, hR, ht0, ht1, hlo, hrep, hbox, hnonzero, hneg, hratio⟩

end RicciFlowSharpEstimate.Geometry
