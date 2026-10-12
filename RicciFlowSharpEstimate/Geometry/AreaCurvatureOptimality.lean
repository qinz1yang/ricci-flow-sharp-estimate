/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvatureVariation
import RicciFlowSharpEstimate.Analysis.AffineIntervalVariation

/-!
# Feasible curvature variations and necessary first-order inequalities

Both moments and the actual curvature box define the feasible parameter set.
One-sided segments and two-sided free directions give different necessary
conditions at a local minimum. No optimizer, multiplier or switching sign is
assumed to exist.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff Topology

/-- Parameters of the literal affine curvature path satisfying the physical
box and both normalized moments. Smoothness of the path is supplied by its inputs. -/
def curvatureParameters (K ξ : ℝ → ℝ) (lo hi : ℝ) : Set ℝ :=
  {t | (∀ x ∈ Set.Icc (0 : ℝ) 1, K x + t * ξ x ∈ Set.Icc lo hi) ∧
    (∫ x in (0 : ℝ)..1, K x + t * ξ x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * (K x + t * ξ x)) = 1}

/-- For a zero-moment direction, feasibility is exactly the remaining box constraint. -/
theorem mem_curvatureParameters_iff (K ξ : ℝ → ℝ) (lo hi t : ℝ)
    (hK : Continuous K) (hξ : Continuous ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) :
    t ∈ curvatureParameters K ξ lo hi ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, K x + t * ξ x ∈ Set.Icc lo hi := by
  obtain ⟨h0, h1⟩ := curvature_moments_add_mul K ξ hK hξ hξ0 hξ1 t
  simp only [curvatureParameters, Set.mem_ofPred_eq, h0, h1, hK0, hK1, and_true]

/-- A segment between two actual box-and-moment curvatures is one-sided feasible. -/
theorem Icc_subset_curvatureParameters_segment (K G : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hG : Continuous G)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hG0 : (∫ x in (0 : ℝ)..1, G x) = 2)
    (hG1 : (∫ x in (0 : ℝ)..1, x * G x) = 1)
    (hKbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Icc lo hi)
    (hGbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, G x ∈ Set.Icc lo hi) :
    Set.Icc (0 : ℝ) 1 ⊆ curvatureParameters K (fun x => G x - K x) lo hi := by
  have hξ0 : (∫ x in (0 : ℝ)..1, G x - K x) = 0 := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable 0 1)
      (hK.intervalIntegrable 0 1), hG0, hK0, sub_self]
  have hξ1 : (∫ x in (0 : ℝ)..1, x * (G x - K x)) = 0 := by
    have hGx : IntervalIntegrable (fun x : ℝ => x * G x) volume 0 1 :=
      (continuous_id.mul hG).intervalIntegrable 0 1
    have hKx : IntervalIntegrable (fun x : ℝ => x * K x) volume 0 1 :=
      (continuous_id.mul hK).intervalIntegrable 0 1
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hGx hKx, hG1, hK1, sub_self]
  intro t ht
  rw [mem_curvatureParameters_iff K (fun x => G x - K x) lo hi t
    hK (hG.sub hK) hK0 hK1 hξ0 hξ1]
  intro x hx
  exact Analysis.add_mul_sub_mem_Icc (hKbox x hx) (hGbox x hx) ht

/-- Strict interior box data give a genuine two-sided neighborhood of feasible parameters. -/
theorem curvatureParameters_mem_nhds_of_interior (K ξ : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hξ : Continuous ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0)
    (hbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Ioo lo hi) :
    curvatureParameters K ξ lo hi ∈ nhds (0 : ℝ) := by
  obtain ⟨δ, hδ, hd⟩ := Analysis.exists_pos_add_mul_mem_Ioo_of_isCompact
    (Set.Icc (0 : ℝ) 1) isCompact_Icc K ξ lo hi hK.continuousOn hξ.continuousOn hbox
  apply Filter.mem_of_superset (Ioo_mem_nhds (neg_neg_of_pos hδ) hδ)
  intro t ht
  rw [mem_curvatureParameters_iff K ξ lo hi t hK hξ hK0 hK1 hξ0 hξ1]
  intro x hx
  exact ⟨(hd t (abs_lt.mpr ht) x hx).1.le, (hd t (abs_lt.mpr ht) x hx).2.le⟩

/-- At a local quotient minimum, every segment to an admissible curvature has
nonnegative mass-corrected switching pairing. No switching sign is assumed. -/
theorem curvature_pairing_nonneg_of_isLocalMinOn_segment (K G r : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hG : Continuous G) (hr : ContDiff ℝ ∞ r)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hG0 : (∫ x in (0 : ℝ)..1, G x) = 2)
    (hG1 : (∫ x in (0 : ℝ)..1, x * G x) = 1)
    (hKbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Icc lo hi)
    (hGbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, G x ∈ Set.Icc lo hi)
    (hmass : 0 < probeMass K r)
    (hmin : IsLocalMinOn (fun t => rayleighQuotient (fun x => K x + t * (G x - K x)) r)
      (curvatureParameters K (fun x => G x - K x) lo hi) 0) :
    0 ≤ ∫ x in (0 : ℝ)..1,
      curvatureLagrangeDensity K r (rayleighQuotient K r) x * (G x - K x) := by
  have hd := rayleighQuotient_curvature_hasDerivAt K r (fun x => G x - K x)
    hK hr (hG.sub hK) hmass.ne'
  have hseg : segment ℝ (0 : ℝ) 1 ⊆ curvatureParameters K (fun x => G x - K x) lo hi := by
    rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_curvatureParameters_segment K G lo hi hK hG hK0 hK1 hG0 hG1 hKbox hGbox
  have hdir : (1 : ℝ) ∈ posTangentConeAt
      (curvatureParameters K (fun x => G x - K x) lo hi) 0 := by
    simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hp := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hdir
  have hp' : 0 ≤ (∫ x in (0 : ℝ)..1,
      curvatureLagrangeDensity K r (rayleighQuotient K r) x * (G x - K x)) /
        probeMass K r := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using hp
  have hi := (le_div_iff₀ hmass).mp hp'
  simpa only [zero_mul] using hi

/-- A two-sided interior direction at a local quotient minimum has zero corrected pairing. -/
theorem curvature_pairing_eq_zero_of_isLocalMinOn_interior (K ξ r : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hξ : Continuous ξ) (hr : ContDiff ℝ ∞ r)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0)
    (hbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Ioo lo hi)
    (hmass : probeMass K r ≠ 0)
    (hmin : IsLocalMinOn (fun t => rayleighQuotient (fun x => K x + t * ξ x) r)
      (curvatureParameters K ξ lo hi) 0) :
    (∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r (rayleighQuotient K r) x * ξ x) = 0 := by
  have hlocal := hmin.isLocalMin
    (curvatureParameters_mem_nhds_of_interior K ξ lo hi hK hξ hK0 hK1 hξ0 hξ1 hbox)
  have hz := hlocal.hasDerivAt_eq_zero (rayleighQuotient_curvature_hasDerivAt K r ξ hK hr hξ hmass)
  exact (div_eq_zero_iff).mp hz |>.resolve_right hmass

/-- Closed support inside the free region gives a two-sided feasible neighborhood,
even when the original curvature touches an obstacle elsewhere. -/
theorem curvatureParameters_mem_nhds_of_free_support (K ξ : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hξ : Continuous ξ)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0)
    (hbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Icc lo hi)
    (hfree : ∀ x ∈ Set.Icc (0 : ℝ) 1 ∩ tsupport ξ, K x ∈ Set.Ioo lo hi) :
    curvatureParameters K ξ lo hi ∈ nhds (0 : ℝ) := by
  obtain ⟨δ, hδ, hd⟩ := Analysis.exists_pos_add_mul_mem_Icc_of_isCompact_of_free_support
    (Set.Icc (0 : ℝ) 1) isCompact_Icc K ξ lo hi hK.continuousOn hξ.continuousOn hbox hfree
  apply Filter.mem_of_superset (Ioo_mem_nhds (neg_neg_of_pos hδ) hδ)
  intro t ht
  rw [mem_curvatureParameters_iff K ξ lo hi t hK hξ hK0 hK1 hξ0 hξ1]
  exact hd t (abs_lt.mpr ht)

/-- A local minimum has zero corrected pairing in every zero-moment direction
whose closed support is contained in the free curvature region. -/
theorem curvature_pairing_eq_zero_of_isLocalMinOn_free_support (K ξ r : ℝ → ℝ) (lo hi : ℝ)
    (hK : Continuous K) (hξ : Continuous ξ) (hr : ContDiff ℝ ∞ r)
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hξ0 : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hξ1 : (∫ x in (0 : ℝ)..1, x * ξ x) = 0)
    (hbox : ∀ x ∈ Set.Icc (0 : ℝ) 1, K x ∈ Set.Icc lo hi)
    (hfree : ∀ x ∈ Set.Icc (0 : ℝ) 1 ∩ tsupport ξ, K x ∈ Set.Ioo lo hi)
    (hmass : probeMass K r ≠ 0)
    (hmin : IsLocalMinOn (fun t => rayleighQuotient (fun x => K x + t * ξ x) r)
      (curvatureParameters K ξ lo hi) 0) :
    (∫ x in (0 : ℝ)..1, curvatureLagrangeDensity K r (rayleighQuotient K r) x * ξ x) = 0 := by
  have hlocal := hmin.isLocalMin
    (curvatureParameters_mem_nhds_of_free_support K ξ lo hi hK hξ hK0 hK1 hξ0 hξ1 hbox hfree)
  have hz := hlocal.hasDerivAt_eq_zero (rayleighQuotient_curvature_hasDerivAt K r ξ hK hr hξ hmass)
  exact (div_eq_zero_iff).mp hz |>.resolve_right hmass

end RicciFlowSharpEstimate.Geometry.AreaProfile
