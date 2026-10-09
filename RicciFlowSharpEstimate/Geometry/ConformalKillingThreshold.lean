/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RepresentedRotationalMetric
import RicciFlowSharpEstimate.Geometry.ConformalKillingSharpness

/-!
# The universal conformal-Killing safe-cap set

The safe set quantifies over every actual represented metric, every positive
curvature box and every original smooth CK form. Transported safety and genuine
smooth witnesses identify this set and its supremum, not merely a named number.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Set Filter DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature Variational
open scoped Manifold ContDiff Topology

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Curvature caps safe for every original smooth CK form on every metric in
the actual represented rotational class, for every admissible curvature box. -/
def conformalKillingSafeCaps : Set ℝ :=
  {C | 1 ≤ C ∧
    ∀ g : SmoothRiemannianMetric (𝓡 2) RotationalSphere,
      IsRepresentedRotationalMetric g →
      ∀ κ Λ : ℝ, 0 < κ →
        (∀ x : RotationalSphere, κ ≤ metricScalarAt g x / 2 ∧
          metricScalarAt g x / 2 ≤ Λ) →
        Λ / κ ≤ C →
        ∀ h : OneFormSection (I := 𝓡 2) (M := RotationalSphere),
          IsConformalKillingOneForm g h → 0 ≤ oneFormDissipation g h}

/-- The actual universal safe-cap set is exactly the closed critical interval. -/
theorem conformalKillingSafeCaps_eq :
    conformalKillingSafeCaps = Icc 1 criticalCap := by
  ext C
  constructor
  · rintro ⟨hC, hsafe⟩
    refine ⟨hC, ?_⟩
    by_contra hcap
    have hgt : criticalCap < C := lt_of_not_ge hcap
    obtain ⟨a, D, _, _, _, _, _, _, hCK, hb, hmid, hneg⟩ :=
      RotationalProfile.exists_negative_unit_meridional_of_criticalCap_lt C hgt
    have hn := hsafe D.metric D.isRepresentedRotationalMetric
      1 ((C + criticalCap) / 2) zero_lt_one hb
      (by simpa only [div_one] using hmid.le)
      (D.meridionalOneForm (fun _ => 1) contDiff_const) hCK
    exact (not_lt_of_ge hn) hneg
  · rintro ⟨hC, hcap⟩
    refine ⟨hC, ?_⟩
    intro g hg κ Λ hκ hb hratio h hCK
    exact hg.oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
      κ Λ hκ hb (hratio.trans hcap) h hCK

/-- The universal CK safety problem has genuine safe caps. -/
theorem conformalKillingSafeCaps_nonempty : conformalKillingSafeCaps.Nonempty := by
  rw [conformalKillingSafeCaps_eq]
  exact ⟨1, le_rfl, one_lt_criticalCap.le⟩

/-- Smooth negative witnesses bound the actual universal safe-cap set above. -/
theorem conformalKillingSafeCaps_bddAbove : BddAbove conformalKillingSafeCaps := by
  rw [conformalKillingSafeCaps_eq]
  exact ⟨criticalCap, fun _ hx => hx.2⟩

/-- The CK threshold is the supremum of the actual universal safe-cap set. -/
def conformalKillingThreshold : ℝ := sSup conformalKillingSafeCaps

/-- The genuine safe-set supremum equals the structurally derived critical cap. -/
theorem conformalKillingThreshold_eq_criticalCap :
    conformalKillingThreshold = criticalCap := by
  apply le_antisymm
  · apply csSup_le conformalKillingSafeCaps_nonempty
    intro C hC
    exact (conformalKillingSafeCaps_eq ▸ hC).2
  · apply le_csSup conformalKillingSafeCaps_bddAbove
    rw [conformalKillingSafeCaps_eq]
    exact ⟨one_lt_criticalCap.le, le_rfl⟩

/-- The radical/exponential formula evaluates the actual universal CK threshold. -/
theorem conformalKillingThreshold_closedForm :
    conformalKillingThreshold =
      ((5 + Real.sqrt 13) / 3) ^ (1 / 3 : ℝ) *
        Real.exp ((4 + 2 * Real.sqrt 13) / 9) := by
  rw [conformalKillingThreshold_eq_criticalCap]
  rfl

/-- Every nonzero original smooth CK form in a safe represented curvature box
has strictly positive action, including at the exact critical cap. -/
theorem IsRepresentedRotationalMetric.oneFormDissipation_pos_of_conformalKilling
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere,
      κ ≤ metricScalarAt g x / 2 ∧ metricScalarAt g x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm g h) (hne : h ≠ 0) :
    0 < oneFormDissipation g h := by
  have hn := hg.oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
    κ Λ hκ hb hcap h hCK
  have heq := hg.oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
    κ Λ hκ hb hcap h hCK
  exact lt_of_le_of_ne hn (fun hz => hne (heq.mp hz.symm))

/-- The already constructed smooth negative witness belongs to this same
represented class, with the exact midpoint curvature cap and fixed unit probe. -/
theorem exists_represented_negative_unit_meridional (C : ℝ) (hC : criticalCap < C) :
    let C₀ := (C + criticalCap) / 2
    ∃ a : ℝ → ℝ, ∃ D : RotationalProfile.PoleData,
      D.a = a ∧ IsRepresentedRotationalMetric D.metric ∧
      ContDiff ℝ ∞ a ∧ Function.Even a ∧
      (∀ v, 1 / C₀ ≤ a v ∧ a v ≤ 1) ∧ RotationalProfile.balance a = 0 ∧
      D.meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 ∧
      IsConformalKillingOneForm D.metric
        (D.meridionalOneForm (fun _ => 1) contDiff_const) ∧
      (∀ x : RotationalSphere, 1 ≤ metricScalarAt D.metric x / 2 ∧
        metricScalarAt D.metric x / 2 ≤ C₀) ∧
      C₀ < C ∧
      oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) < 0 := by
  obtain ⟨a, D, ha, hrest⟩ :=
    RotationalProfile.exists_negative_unit_meridional_of_criticalCap_lt C hC
  exact ⟨a, D, ha, D.isRepresentedRotationalMetric, hrest⟩

/-- The same critical recovery sequence lies in the represented class and
retains its fixed nonzero unit CK probes, positive actions and zero action limit. -/
theorem exists_represented_critical_unit_probe_recovery :
    ∃ A : ℕ → ℝ → ℝ, ∃ D : ℕ → RotationalProfile.PoleData,
      (∀ n, (D n).a = A n ∧ IsRepresentedRotationalMetric (D n).metric ∧
        ContDiff ℝ ∞ (A n) ∧ Function.Even (A n) ∧
        (∀ v, 1 / criticalCap ≤ A n v ∧ A n v ≤ 1) ∧
        RotationalProfile.balance (A n) = 0 ∧
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
  obtain ⟨A, D, hA, hlim, hQ⟩ := RotationalProfile.exists_critical_unit_probe_recovery
  exact ⟨A, D, fun n => ⟨(hA n).1, (D n).isRepresentedRotationalMetric, (hA n).2⟩,
    hlim, hQ⟩

end RicciFlowSharpEstimate.Geometry
