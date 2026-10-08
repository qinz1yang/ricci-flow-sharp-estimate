/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.PairFunctional
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

/-!
# Rigidity of the actual exponential pair remainder

For profiles continuous on the unit interval, the actual triangular remainder
vanishes precisely when their difference is constant on that interval. The
proof derives almost-everywhere vanishing from integrability and nonnegativity,
uses positivity of Lebesgue measure on open sets inside the triangle, and then
extends constancy to the endpoints by continuity.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

private theorem continuousOn_profileDifference {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 - f p.2) (Icc (0, 0) (1, 1)) := by
  apply ContinuousOn.sub
  · exact hf.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)
  · exact hf.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩)

private theorem difference_eq_on_openTriangle (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hzero : pairRemainder k g = 0) :
    ∀ v s : ℝ, 0 < v → v < s → s < 1 → k v - g v = k s - g s := by
  let R : ℝ × ℝ → ℝ := fun p => 2 * p.2 * Real.exp (g p.1 - g p.2) *
    (Real.exp ((k p.1 - g p.1) - (k p.2 - g p.2)) - 1 -
      ((k p.1 - g p.1) - (k p.2 - g p.2)))
  have hTS : orderedTriangle ⊆ Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
    rintro p ⟨h0, h12, h1⟩
    exact ⟨⟨h0, h0.trans h12.le⟩, ⟨h12.le.trans h1, h1⟩⟩
  have hgdiff := continuousOn_profileDifference hg
  have hδdiff := continuousOn_profileDifference (hk.sub hg)
  have hRcont : ContinuousOn R (Icc (0, 0) (1, 1)) :=
    ((continuous_const.mul continuous_snd).continuousOn.mul
      (Real.continuous_exp.comp_continuousOn hgdiff)).mul
      (((Real.continuous_exp.comp_continuousOn hδdiff).sub continuousOn_const).sub hδdiff)
  have hRint : IntegrableOn R orderedTriangle :=
    (hRcont.integrableOn_compact isCompact_Icc).mono_set hTS
  have hRnonneg : 0 ≤ᵐ[volume.restrict orderedTriangle] R := by
    filter_upwards [ae_restrict_mem measurableSet_orderedTriangle] with p hp
    dsimp only [R]
    have hs : 0 ≤ p.2 := hp.1.trans hp.2.1.le
    apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (Real.exp_pos _).le)
    have h := Real.add_one_le_exp ((k p.1 - g p.1) - (k p.2 - g p.2))
    linarith
  have hRzero : (∫ p in orderedTriangle, R p) = 0 := hzero
  have hAE : R =ᵐ[volume.restrict orderedTriangle] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hRnonneg hRint).mp hRzero
  let U : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hUT : U ⊆ orderedTriangle := by
    rintro p ⟨h0, h12, h1⟩
    exact ⟨h0.le, h12, h1.le⟩
  have hpoint : EqOn R 0 U :=
    Measure.eqOn_open_of_ae_eq
      (ae_restrict_of_ae_restrict_of_subset hUT hAE) hU
      (hRcont.mono (hUT.trans hTS)) continuousOn_const
  intro v s hv hvs hs
  have hRpoint : R (v, s) = 0 := hpoint ⟨hv, hvs, hs⟩
  dsimp only [R] at hRpoint
  have hweight : 0 < 2 * s * Real.exp (g v - g s) :=
    mul_pos (mul_pos (by norm_num) (hv.trans hvs)) (Real.exp_pos _)
  have hrem : Real.exp ((k v - g v) - (k s - g s)) - 1 -
      ((k v - g v) - (k s - g s)) = 0 :=
    (mul_eq_zero.mp hRpoint).resolve_left hweight.ne'
  by_contra hneq
  have hstrict := Real.add_one_lt_exp (sub_ne_zero.mpr hneq)
  linarith

/-- The actual pair remainder vanishes exactly along constant differences on the unit interval. -/
theorem pairRemainder_eq_zero_iff (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    pairRemainder k g = 0 ↔ ∃ c : ℝ, ∀ v ∈ Icc (0 : ℝ) 1, k v - g v = c := by
  constructor
  · intro hzero
    have hpair := difference_eq_on_openTriangle k g hk hg hzero
    obtain ⟨a, ha0, ha1⟩ := exists_between (zero_lt_one : (0 : ℝ) < 1)
    refine ⟨k a - g a, ?_⟩
    have hinterior : EqOn (fun v => k v - g v) (fun _ => k a - g a) (Ioo (0 : ℝ) 1) := by
      intro v hv
      rcases lt_trichotomy v a with h | rfl | h
      · exact hpair v a hv.1 h ha1
      · rfl
      · exact (hpair a v ha0 h hv.2).symm
    exact hinterior.of_subset_closure (hk.sub hg) continuousOn_const
      (fun _ hv => ⟨hv.1.le, hv.2.le⟩)
      (closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)).symm.subset
  · rintro ⟨c, hc⟩
    calc
      pairRemainder k g = ∫ p in orderedTriangle, (0 : ℝ) := by
        unfold pairRemainder
        apply setIntegral_congr_fun measurableSet_orderedTriangle
        intro p hp
        dsimp only
        rw [hc p.1 ⟨hp.1, hp.2.1.le.trans hp.2.2⟩,
          hc p.2 ⟨hp.1.trans hp.2.1.le, hp.2.2⟩]
        simp
      _ = 0 := by simp

end RicciFlowSharpEstimate.Variational
