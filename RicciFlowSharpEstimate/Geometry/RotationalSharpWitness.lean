/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaGeometricRealization
import RicciFlowSharpEstimate.Geometry.SmoothAreaSafety

/-!
# Smooth negative witnesses at every strictly superthreshold cap

The negative smooth infimum supplies an actual unit-mass competitor at a cap
strictly between the original threshold and any prescribed larger cap. The
same curvature and probe enter the original smooth geometric realization,
retaining all coordinate, derivative, curvature and dissipation equations.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

/-- Every cap above the original rotational threshold admits an actual smooth
unit-mass competitor with negative complete action. -/
theorem exists_smooth_area_competitor_action_neg_of_rotationalThreshold_lt
    {C : ℝ} (hC : rotationalThreshold < C) :
    ∃ K r : ℝ → ℝ,
      IsSmoothAreaCompetitor C K r ∧ meridionalAction K r < 0 := by
  obtain ⟨a, ⟨K, r, h, rfl⟩, ha⟩ := exists_lt_of_csInf_lt
    (smoothAreaActionValues_nonempty C (one_le_rotationalThreshold.trans hC.le))
    (smoothAreaInfimum_neg_of_rotationalThreshold_lt hC)
  exact ⟨K, r, h, ha⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile

namespace RicciFlowSharpEstimate.Geometry

open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature AreaProfile
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Every cap strictly above the original threshold admits an original smooth
represented rotational metric with a positive curvature ratio strictly below
that cap and a nonzero smooth form of negative dissipation. The exact normalized
curvature and probe, both inverse maps, all probe jets and the same-metric
dissipation equation remain tied to the original geometric producers. -/
theorem exists_smooth_geometric_negative_witness_of_rotationalThreshold_lt
    {D : ℝ} (hD : rotationalThreshold < D) :
    ∃ (C κ Λ : ℝ) (K r X : ℝ → ℝ) (P : RotationalProfile.PoleData)
      (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R),
      rotationalThreshold < C ∧ C < D ∧
      IsSmoothAreaCompetitor C K r ∧
      0 < κ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ) ∧
      Λ / κ ≤ C ∧ Λ / κ < D ∧
      (∫ x in (0 : ℝ)..1, K x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧
      probeMass K r = 1 ∧ meridionalAction K r < 0 ∧
      ContDiff ℝ ∞ X ∧
      heightCoordinate K 0 = -1 ∧ heightCoordinate K 1 = 1 ∧
      X (-1) = 0 ∧ X 1 = 1 ∧
      MapsTo (heightCoordinate K) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
      MapsTo X (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        X (heightCoordinate K x) = x ∧
        P.a (heightCoordinate K x) = 1 / K x ∧
        R (heightCoordinate K x) = r x ∧
        RotationalProfile.warp P.a (heightCoordinate K x) = warp K x) ∧
      (∀ v ∈ Icc (-1 : ℝ) 1,
        heightCoordinate K (X v) = v ∧ deriv X v * K (X v) = 1) ∧
      R = r ∘ X ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        deriv P.a (heightCoordinate K x) = -deriv K x / K x ^ 3 ∧
        deriv R (heightCoordinate K x) = deriv r x / K x ∧
        deriv (deriv R) (heightCoordinate K x) =
          deriv (deriv r) x / K x ^ 2 - deriv r x * deriv K x / K x ^ 3) ∧
      (∀ p : RotationalSphere,
        metricScalarAt P.metric p / 2 = K (X (sphereHeight p))) ∧
      oneFormDissipation P.metric (P.meridionalOneForm R hR) =
        2 * Real.pi * meridionalAction K r ∧
      IsRepresentedRotationalMetric P.metric ∧
      (∀ p : RotationalSphere,
        κ ≤ metricScalarAt P.metric p / 2 ∧ metricScalarAt P.metric p / 2 ≤ Λ) ∧
      P.meridionalOneForm R hR ≠ 0 ∧
      oneFormDissipation P.metric (P.meridionalOneForm R hR) < 0 := by
  obtain ⟨C, hC, hCD⟩ := exists_between hD
  obtain ⟨K, r, hcomp, hnegArea⟩ :=
    exists_smooth_area_competitor_action_neg_of_rotationalThreshold_lt hC
  have hdata := hcomp
  rcases hdata with ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, hmass⟩
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < K x :=
    hκ.trans_le (hbox x hx).1
  obtain ⟨X, P, R, hR, hX, hV0, hV1, hX0, hX1, hVmap, hXmap,
    hforward, hbackward, hcompR, hjets, hcurv, haction⟩ :=
    exists_smooth_geometric_realization K r hK hr hpos hzero hone
  have hneg : oneFormDissipation P.metric (P.meridionalOneForm R hR) < 0 := by
    rw [haction]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hnegArea
  have hnonzero : P.meridionalOneForm R hR ≠ 0 := by
    intro hz
    have h := hneg
    rw [hz, oneFormDissipation_zero] at h
    exact (lt_irrefl 0) h
  have hgeobox (p : RotationalSphere) :
      κ ≤ metricScalarAt P.metric p / 2 ∧ metricScalarAt P.metric p / 2 ≤ Λ := by
    rw [hcurv p]
    exact hbox _ (hXmap (sphereHeight_mem_Icc p))
  exact ⟨C, κ, Λ, K, r, X, P, R, hR, hC, hCD, hcomp, hκ, hbox, hratio,
    hratio.trans_lt hCD, hzero, hone, hmass, hnegArea, hX, hV0, hV1, hX0, hX1,
    hVmap, hXmap, hforward, hbackward, hcompR, hjets, hcurv, haction,
    P.isRepresentedRotationalMetric, hgeobox, hnonzero, hneg⟩

end RicciFlowSharpEstimate.Geometry
