/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Smooth approximation of bounded L2 functions

A real L2 function taking values almost everywhere in a closed interval on
the physical unit interval admits globally smooth approximations in every
slightly enlarged interval. The interval endpoints may coincide.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem abs_sub_clamp_le {a b z y : ℝ} (ha : a ≤ z) (hb : z ≤ b) :
    |z - max a (min b y)| ≤ |z - y| := by
  by_cases hya : y < a
  · have hyb : y ≤ b := hya.le.trans (ha.trans hb)
    rw [min_eq_right hyb, max_eq_left hya.le]
    rw [abs_of_nonneg (sub_nonneg.mpr ha),
      abs_of_nonneg (sub_nonneg.mpr (hya.le.trans ha))]
    linarith
  · have hay : a ≤ y := le_of_not_gt hya
    by_cases hby : b < y
    · rw [min_eq_left hby.le, max_eq_right (ha.trans hb)]
      rw [abs_of_nonpos (sub_nonpos.mpr hb),
        abs_of_nonpos (sub_nonpos.mpr (hb.trans hby.le))]
      linarith
    · have hyb : y ≤ b := le_of_not_gt hby
      simp only [min_eq_right hyb, max_eq_right hay, le_refl]

/-- Every L2 function whose values lie almost everywhere in a closed interval
on `(0, 1)` admits a globally smooth L2 approximation whose values everywhere
lie in the interval enlarged by the prescribed positive error. -/
theorem exists_contDiff_approx_Icc_of_memLp
    (f : ℝ → ℝ) (a b ε : ℝ) (hab : a ≤ b) (hf : MemLp f 2 areaμ)
    (hbox : ∀ᵐ x ∂areaμ, f x ∈ Icc a b) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x, g x ∈ Icc (a - ε) (b + ε)) ∧
      eLpNorm (f - g) 2 areaμ ≤ ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨g₀, -, hg₀, hfg₀⟩ :=
    hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hhalf
  let h : ℝ → ℝ := fun x => max a (min b (g₀ x))
  have hh : Continuous h :=
    continuous_const.max (continuous_const.min hg₀.continuous)
  have hhbox (x : ℝ) : h x ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hfh : eLpNorm (f - h) 2 areaμ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_mono_ae
      (hf.aestronglyMeasurable.sub hh.aestronglyMeasurable) ?_).trans hfg₀
    filter_upwards [hbox] with x hx
    simpa only [Pi.sub_apply, Real.norm_eq_abs, h] using
      (abs_sub_clamp_le (y := g₀ x) hx.1 hx.2)
  obtain ⟨g, hg, hgdist, -⟩ :=
    hh.exists_contDiff_approx ⊤ (ε := fun _ => ε / 2) continuous_const
      (fun _ => hhalf)
  have hunit : areaμ univ = 1 := by
    simp [Real.volume_Ioo]
  have hgh : eLpNorm (g - h) 2 areaμ ≤ ENNReal.ofReal (ε / 2) := by
    have hbound : ∀ᵐ x ∂areaμ, ‖(g - h) x‖ ≤ ε / 2 := by
      apply Filter.Eventually.of_forall
      intro x
      simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.dist_eq] using (hgdist x).le
    simpa [hunit] using
      (eLpNorm_le_of_ae_bound (p := 2)
        (hg.continuous.sub hh).aestronglyMeasurable hbound)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    have hdist : |g x - h x| < ε / 2 := by
      simpa only [Real.dist_eq] using hgdist x
    obtain ⟨hl, hu⟩ := abs_lt.mp hdist
    obtain ⟨hlo, hhi⟩ := hhbox x
    constructor <;> linarith
  · have hdecomp : f - g = (f - h) - (g - h) := by simp
    calc
      eLpNorm (f - g) 2 areaμ = eLpNorm ((f - h) - (g - h)) 2 areaμ := by
        rw [hdecomp]
      _ ≤ eLpNorm (f - h) 2 areaμ + eLpNorm (g - h) 2 areaμ :=
        eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hfh hgh
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

end RicciFlowSharpEstimate.Analysis
