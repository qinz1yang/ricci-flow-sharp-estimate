/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery
import RicciFlowSharpEstimate.Geometry.CriticalCurvatureContraction

/-!
# Exact-moment recovery of a negative complete area action

The probe remains fixed while symmetric monotone curvature polynomials recover
both moments inside the identical box. Convergence of the complete density
selects an actually negative smooth member of the recovered sequence.

Adapted from Ziyang Qin's historical smooth meridian strict witness recovery,
retaining the original smooth probe instead of introducing independent jets.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-- A negative action with one fixed smooth probe survives exact-moment smooth
curvature recovery in the identical symmetric monotone box. -/
theorem exists_smooth_negative_action_of_symmetric_box
    (K r : ℝ → ℝ) (hK : Continuous K) (hr : ContDiff ℝ ∞ r)
    (lo hi : ℝ) (hlo : lo < 2) (hhi : 2 < hi)
    (hSymm : ∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x)
    (hMono : MonotoneOn K (Icc (1 / 2 : ℝ) 1))
    (hMoment : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi)
    (hNeg : meridionalAction K r < 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧
      (∀ x ∈ Icc (0 : ℝ) 1, G (1 - x) = G x) ∧
      MonotoneOn G (Icc (1 / 2 : ℝ) 1) ∧
      AntitoneOn G (Icc (0 : ℝ) (1 / 2)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc lo hi) ∧
      (∫ x in (0 : ℝ)..1, G x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * G x) = 1 ∧ meridionalAction G r < 0 := by
  obtain ⟨G, hG, hL1, ns, hns, hae⟩ :=
    Analysis.SymmetricMomentRecovery.exists_smooth_exactMoments_mem_box_l1_ae
      2 lo hi hlo hhi K (hK.comp continuous_subtype_val).stronglyMeasurable
      hSymm hMono hMoment hBox
  have hBound (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      |G (ns n) x| ≤ max |lo| |hi| := by
    obtain ⟨_, _, _, _, hb, _, _⟩ := hG (ns n)
    exact abs_le_max_abs_abs (hb x hx).1 (hb x hx).2
  have hAction := tendsto_meridionalAction_of_l1_of_ae (fun n => G (ns n)) K r
    (fun n => (hG (ns n)).1.continuous) hK hr (max |lo| |hi|) hBound
    (hL1.comp hns.tendsto_atTop) hae
  have hEventually : ∀ᶠ n in atTop, meridionalAction (G (ns n)) r < 0 :=
    hAction.eventually (gt_mem_nhds hNeg)
  obtain ⟨n, hn⟩ := hEventually.exists
  obtain ⟨hsmooth, hsymm, hmono, hanti, hbox, hzero, hone⟩ := hG (ns n)
  refine ⟨G (ns n), hsmooth, hsymm, hmono, hanti, hbox, hzero, ?_, hn⟩
  norm_num at hone
  exact hone

end RicciFlowSharpEstimate.Geometry.AreaProfile

namespace RicciFlowSharpEstimate.Geometry.CriticalAreaProfile

open Filter MeasureTheory Set Variational
open scoped ContDiff Topology

/-- The same critical plateau probe has negative action for a globally smooth
exact-moment curvature in the identical strictly contracted box. -/
theorem exists_smooth_negative_area_data :
    ∃ (r : ℝ → ℝ) (t : ℝ) (K : ℝ → ℝ),
      ContDiff ℝ ∞ r ∧ r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧ 0 < t ∧ t < 1 ∧
      0 < contractedLower t ∧ contractedUpper t / contractedLower t < criticalCap ∧
      ContDiff ℝ ∞ K ∧
      (∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc (contractedLower t) (contractedUpper t)) ∧
      (∫ x in (0 : ℝ)..1, K x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x) ∧
      MonotoneOn K (Icc (1 / 2 : ℝ) 1) ∧
      AntitoneOn K (Icc (0 : ℝ) (1 / 2)) ∧ AreaProfile.meridionalAction K r < 0 := by
  obtain ⟨r, t, hr, hr0, hrd0, hn0, hn1, hnonconstant, ht0, ht1,
    hlo, hlo2, hhi2, hratio, hneg⟩ := exists_smooth_negative_contraction
  obtain ⟨K, hK, hsymm, hmono, hanti, hbox, hzero, hone, hnegK⟩ :=
    AreaProfile.exists_smooth_negative_action_of_symmetric_box
      (contractedCurvature t) r (contractedCurvature_continuous t) hr
      (contractedLower t) (contractedUpper t) hlo2 hhi2
      (contractedCurvature_reflection t) (contractedCurvature_monotoneOn_right t ht1.le)
      (contractedCurvature_moments t).1
      (fun x _ => contractedCurvature_bounds t ht1.le x) hneg
  exact ⟨r, t, K, hr, hr0, hrd0, hn0, hn1, hnonconstant, ht0, ht1,
    hlo, hratio, hK, hbox, hzero, hone, hsymm, hmono, hanti, hnegK⟩

end RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
