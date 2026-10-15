/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicGraphCutoff
import RicciFlowSharpEstimate.Analysis.ParabolicGraphClosed
import RicciFlowSharpEstimate.Analysis.ParabolicGraphAddition
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Simultaneous smooth recovery of the two cuts at a double zero

One unbounded selection from the original smooth probe sequence recovers both
literal cuts. The two smooth probes sum to that selected original probe at
every index. Any accompanying curvature sequence can therefore be composed
with this same selection without changing its cap, moments, or limit.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem exists_diagonal_tendsto_zero
    (e : ℕ → ℕ → ℝ≥0∞) (he : ∀ n, Tendsto (e n) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, (∀ n, n ≤ m n) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun n ↦ e n (m n)) atTop (𝓝 0) := by
  have hchoice (n : ℕ) : ∃ k : ℕ, n ≤ k ∧ e n k < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    have htol : (0 : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by simp
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((he n).eventually (gt_mem_nhds htol))
    exact ⟨max n N, le_max_left _ _, hN _ (le_max_right _ _)⟩
  choose m hm hsmall using hchoice
  have htol : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine ⟨m, hm, tendsto_atTop_mono hm tendsto_id, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htol
    (fun _ ↦ zero_le) (fun n ↦ (hsmall n).le)

private theorem strong_two_limit_of_triangle
    {f g : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g n) 2 areaμ) atTop (𝓝 0))
    (hgu : Tendsto (fun n ↦ eLpNorm (g n - u) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n - u) 2 areaμ) atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n ↦ eLpNorm (f n - g n) 2 areaμ + eLpNorm (g n - u) 2 areaμ)
      atTop (𝓝 0) := by simpa only [zero_add] using hfg.add hgu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ ↦ zero_le) ?_
  intro n
  have heq : f n - u = (f n - g n) + (g n - u) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  change eLpNorm (f n - u) 2 areaμ ≤
    eLpNorm (f n - g n) 2 areaμ + eLpNorm (g n - u) 2 areaμ
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- At a double zero, both literal cuts have genuine weak graphs and share a
smooth recovery obtained from one unbounded selection of the supplied original
smooth sequence. The smooth left probe is the displayed cutoff product; the
right probe is its exact complement in that same selected original probe.
All six actual derivative-graph limits are retained before any normalization. -/
theorem exists_smooth_cut_parabolicGraph_recovery
    {rs : ℕ → ℝ → ℝ} {r p z : ℝ → ℝ} {c : ℝ}
    (hrs : ∀ n, ContDiff ℝ ∞ (rs n))
    (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrc : r c = 0) (hpc : p c = 0)
    (hR : Tendsto (fun n ↦ eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0))
    (hP : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0))
    (hZ : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
      atTop (𝓝 0)) :
    let rL := fun x ↦ if x < c then r x else 0
    let pL := fun x ↦ if x < c then p x else 0
    let zL := fun x ↦ if x < c then z x else 0
    HasParabolicWeakDerivatives rL pL zL ∧
    HasParabolicWeakDerivatives (r - rL) (p - pL) (z - zL) ∧
    ∃ (m : ℕ → ℕ) (us vs : ℕ → ℝ → ℝ),
      (∀ n, n ≤ m n) ∧ Tendsto m atTop atTop ∧
      (∀ n x, us n x = rs (m n) x * smoothLeftCutoff c ((c / 2) / ((n : ℝ) + 1)) x) ∧
      (∀ n, vs n = rs (m n) - us n) ∧
      (∀ n, ContDiff ℝ ∞ (us n)) ∧ (∀ n, ContDiff ℝ ∞ (vs n)) ∧
      Tendsto (fun n ↦ eLpNorm (us n - rL) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (us n) x) -
          (fun x ↦ Real.sqrt (x * (1 - x)) * pL x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (us n)) x) -
          (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * zL x)) 2 areaμ)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (vs n - (r - rL)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (vs n) x) -
          (fun x ↦ Real.sqrt (x * (1 - x)) * (p - pL) x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (vs n)) x) -
          (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * (z - zL) x)) 2 areaμ)
        atTop (𝓝 0) := by
  dsimp only
  let rL : ℝ → ℝ := fun x ↦ if x < c then r x else 0
  let pL : ℝ → ℝ := fun x ↦ if x < c then p x else 0
  let zL : ℝ → ℝ := fun x ↦ if x < c then z x else 0
  let ε : ℕ → ℝ := fun n ↦ (c / 2) / ((n : ℝ) + 1)
  let χ : ℕ → ℝ → ℝ := fun n ↦ smoothLeftCutoff c (ε n)
  have hε (n : ℕ) : 0 < ε n :=
    div_pos (div_pos hc.1 (by norm_num)) (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c / 2)
  have hχ (n : ℕ) : ContDiff ℝ ∞ (χ n) := contDiff_smoothLeftCutoff c (ε n)
  let R : ℕ → ℝ → ℝ := fun n x ↦ r x * χ n x
  let P : ℕ → ℝ → ℝ := fun n x ↦ p x * χ n x + r x * deriv (χ n) x
  let Z : ℕ → ℝ → ℝ := fun n x ↦ z x * χ n x + 2 * p x * deriv (χ n) x +
    r x * deriv (deriv (χ n)) x
  have hweak := parabolicGraph_tendsto_smoothLeftCutoff h hr hp hc hrc hpc hε hεlim
  have hleft : HasParabolicWeakDerivatives rL pL zL :=
    hasParabolicWeakDerivatives_of_strong_graph (fun n ↦ h.mul_contDiff (χ n) (hχ n))
      hweak.1 hweak.2.1 hweak.2.2
  have hright : HasParabolicWeakDerivatives (r - rL) (p - pL) (z - zL) := by
    change HasParabolicWeakDerivatives (fun x ↦ r x - rL x)
      (fun x ↦ p x - pL x) (fun x ↦ z x - zL x)
    simpa only [neg_one_mul, sub_eq_add_neg] using h.add (hleft.const_mul (-1))
  let U : ℕ → ℕ → ℝ → ℝ := fun n k x ↦ rs k x * χ n x
  have hU (n k : ℕ) : ContDiff ℝ ∞ (U n k) := (hrs k).mul (hχ n)
  have hfixed (n : ℕ) := parabolicGraph_tendsto_mul_contDiff
    (fun k ↦ (hrs k).of_le (by simp)) h hR hP hZ (χ n) (hχ n)
  let er : ℕ → ℕ → ℝ≥0∞ := fun n k ↦ eLpNorm (U n k - R n) 2 areaμ
  let ep : ℕ → ℕ → ℝ≥0∞ := fun n k ↦ eLpNorm
    ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (U n k) x) -
      (fun x ↦ Real.sqrt (x * (1 - x)) * P n x)) 2 areaμ
  let ez : ℕ → ℕ → ℝ≥0∞ := fun n k ↦ eLpNorm
    ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (U n k)) x) -
      (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * Z n x)) 2 areaμ
  let e : ℕ → ℕ → ℝ≥0∞ := fun n k ↦ er n k + ep n k + ez n k
  have helim (n : ℕ) : Tendsto (e n) atTop (𝓝 0) := by
    simpa only [zero_add] using ((hfixed n).1.add (hfixed n).2.1).add (hfixed n).2.2
  obtain ⟨m, hm, hmtop, hem⟩ := exists_diagonal_tendsto_zero e helim
  have herm : Tendsto (fun n ↦ er n (m n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hem
      (fun _ ↦ zero_le) ?_
    intro n
    exact (le_add_of_nonneg_right (show 0 ≤ ep n (m n) from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ ez n (m n) from zero_le))
  have hepm : Tendsto (fun n ↦ ep n (m n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hem
      (fun _ ↦ zero_le) ?_
    intro n
    exact (le_add_of_nonneg_left (show 0 ≤ er n (m n) from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ ez n (m n) from zero_le))
  have hezm : Tendsto (fun n ↦ ez n (m n)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hem
      (fun _ ↦ zero_le) (fun n ↦ le_add_of_nonneg_left
        (show 0 ≤ er n (m n) + ep n (m n) from zero_le))
  let us : ℕ → ℝ → ℝ := fun n ↦ U n (m n)
  let vs : ℕ → ℝ → ℝ := fun n ↦ rs (m n) - us n
  have hus (n : ℕ) : ContDiff ℝ ∞ (us n) := hU n (m n)
  have hvs (n : ℕ) : ContDiff ℝ ∞ (vs n) := (hrs (m n)).sub (hus n)
  have huR : Tendsto (fun n ↦ eLpNorm (us n - rL) 2 areaμ) atTop (𝓝 0) :=
    strong_two_limit_of_triangle herm hweak.1
  have huP : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (us n) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * pL x)) 2 areaμ) atTop (𝓝 0) :=
    strong_two_limit_of_triangle hepm hweak.2.1
  have huZ : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (us n)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * zL x)) 2 areaμ)
      atTop (𝓝 0) := strong_two_limit_of_triangle hezm hweak.2.2
  have hneg := parabolicGraph_tendsto_const_mul
    (fun n ↦ (hus n).of_le (by simp)) hleft
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1))) huR huP huZ
  have hrightLimits := parabolicGraph_tendsto_add
    (fun n ↦ (hrs (m n)).of_le (by simp))
    (fun n ↦ (contDiff_const.mul (hus n)).of_le (by simp))
    (hR.comp hmtop) (hP.comp hmtop) (hZ.comp hmtop) hneg.1 hneg.2.1 hneg.2.2
  refine ⟨hleft, hright, m, us, vs, hm, hmtop, fun _ _ ↦ rfl, fun _ ↦ rfl,
    hus, hvs, huR, huP, huZ, ?_, ?_, ?_⟩
  · simpa only [vs, rL, neg_one_mul, ← sub_eq_add_neg, Pi.sub_def] using
      hrightLimits.1
  · simpa only [vs, pL, neg_one_mul, ← sub_eq_add_neg, Pi.sub_def] using
      hrightLimits.2.1
  · simpa only [vs, zL, neg_one_mul, ← sub_eq_add_neg, Pi.sub_def] using
      hrightLimits.2.2

end RicciFlowSharpEstimate.Analysis
