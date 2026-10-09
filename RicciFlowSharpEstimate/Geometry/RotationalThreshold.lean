/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConstantCurvatureDissipation
import RicciFlowSharpEstimate.Geometry.StrictRotationalWitness

/-!
# Structural strict separation of rotational dissipation thresholds

The unrestricted safe-cap set quantifies over every original smooth one-form
in the same represented metric class. Constant-curvature Green integration
proves cap-one safety. The recovered smooth negative witness bounds its real
supremum strictly below the actual conformal-Killing threshold.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Set DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature CriticalAreaProfile
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Curvature caps safe for every original smooth one-form on every metric in
the represented rotational class, in every positive actual curvature box. -/
def rotationalSafeCaps : Set ℝ :=
  {C | 1 ≤ C ∧
    ∀ g : SmoothRiemannianMetric (𝓡 2) RotationalSphere,
      IsRepresentedRotationalMetric g →
      ∀ κ Λ : ℝ, 0 < κ →
        (∀ x : RotationalSphere, κ ≤ metricScalarAt g x / 2 ∧
          metricScalarAt g x / 2 ≤ Λ) →
        Λ / κ ≤ C →
        ∀ h : OneFormSection (I := 𝓡 2) (M := RotationalSphere),
          0 ≤ oneFormDissipation g h}

/-- A positive box of ratio at most one forces constant curvature, and the
actual Green square identity proves safety for every original smooth form. -/
theorem one_mem_rotationalSafeCaps : (1 : ℝ) ∈ rotationalSafeCaps := by
  refine ⟨le_rfl, ?_⟩
  intro g _hg κ Λ hκ hbox hratio h
  have hΛ : Λ ≤ κ := (div_le_one hκ).mp hratio
  have hconstant (x : RotationalSphere) : metricScalarAt g x / 2 = κ :=
    le_antisymm ((hbox x).2.trans hΛ) (hbox x).1
  exact oneFormDissipation_nonneg_of_constant_curvature g κ hκ.le hconstant h

/-- The all-form universal safety problem has a genuine nonempty safe set. -/
theorem rotationalSafeCaps_nonempty : rotationalSafeCaps.Nonempty :=
  ⟨1, one_mem_rotationalSafeCaps⟩

/-- Universal all-form safety is downward closed among caps at least one. -/
theorem rotationalSafeCaps_downward {C D : ℝ} (hC : C ∈ rotationalSafeCaps)
    (hD : 1 ≤ D) (hDC : D ≤ C) : D ∈ rotationalSafeCaps := by
  refine ⟨hD, ?_⟩
  intro g hg κ Λ hκ hbox hratio h
  exact hC.2 g hg κ Λ hκ hbox (hratio.trans hDC) h

/-- The same recovered original-metric witness excludes all caps at or above
one strictly subcritical contracted ratio. -/
theorem exists_contracted_bound_for_rotationalSafeCaps :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      contractedUpper t / contractedLower t < conformalKillingThreshold ∧
      ∀ C ∈ rotationalSafeCaps, C < contractedUpper t / contractedLower t := by
  obtain ⟨t, D, R, hR, ht0, ht1, hlo, hrep, hbox, _hnonzero, hneg, hratio⟩ :=
    exists_negative_rotational_below_conformalKillingThreshold
  refine ⟨t, ⟨ht0, ht1⟩, hratio, ?_⟩
  intro C hC
  by_contra hn
  have hratioC : contractedUpper t / contractedLower t ≤ C := le_of_not_gt hn
  have hsafe := hC.2 D.metric hrep (contractedLower t) (contractedUpper t)
    hlo hbox hratioC (D.meridionalOneForm R hR)
  exact (not_lt_of_ge hsafe) hneg

/-- The genuine negative witness bounds the unrestricted universal safe set. -/
theorem rotationalSafeCaps_bddAbove : BddAbove rotationalSafeCaps := by
  obtain ⟨t, _ht, _hratio, hbound⟩ := exists_contracted_bound_for_rotationalSafeCaps
  exact ⟨contractedUpper t / contractedLower t, fun C hC => (hbound C hC).le⟩

/-- The unrestricted rotational threshold is the supremum of its actual safe caps. -/
def rotationalThreshold : ℝ := sSup rotationalSafeCaps

/-- Cap-one safety gives a nonvacuous lower bound for the unrestricted threshold. -/
theorem one_le_rotationalThreshold : 1 ≤ rotationalThreshold :=
  le_csSup rotationalSafeCaps_bddAbove one_mem_rotationalSafeCaps

/-- An actual contracted curvature box bounds the unrestricted supremum strictly
below the conformal-Killing threshold. -/
theorem exists_contracted_ratio_above_rotationalThreshold :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      rotationalThreshold ≤ contractedUpper t / contractedLower t ∧
      contractedUpper t / contractedLower t < conformalKillingThreshold := by
  obtain ⟨t, ht, hratio, hbound⟩ := exists_contracted_bound_for_rotationalSafeCaps
  exact ⟨t, ht, csSup_le rotationalSafeCaps_nonempty (fun C hC => (hbound C hC).le), hratio⟩

/-- The unrestricted rotational threshold is strictly smaller than the actual
universal conformal-Killing threshold. -/
theorem rotationalThreshold_lt_conformalKillingThreshold :
    rotationalThreshold < conformalKillingThreshold := by
  obtain ⟨_t, _ht, hbound, hstrict⟩ := exists_contracted_ratio_above_rotationalThreshold
  exact hbound.trans_lt hstrict

end RicciFlowSharpEstimate.Geometry
