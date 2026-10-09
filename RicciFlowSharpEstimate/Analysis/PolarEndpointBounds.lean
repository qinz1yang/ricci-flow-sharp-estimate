/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform bounds at polar endpoints

A twice continuously differentiable function vanishing at both radial endpoints
is bounded by the sine of its radial coordinate, uniformly on every compact
angular interval. The same estimate holds for its angular derivative.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set
open scoped ContDiff

/-- Joint regularity of differentiation in the first coordinate. -/
theorem contDiff_deriv_fst {q : ℝ × ℝ → ℝ} {m n : ℕ∞ω}
    (hq : ContDiff ℝ n q) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (fun x : ℝ × ℝ => deriv (fun t => q (t, x.2)) x.1) := by
  unfold deriv
  exact (hq.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))).fderiv_apply
    contDiff_fst contDiff_const hmn

/-- Joint regularity of differentiation in the second coordinate. -/
theorem contDiff_deriv_snd {q : ℝ × ℝ → ℝ} {m n : ℕ∞ω}
    (hq : ContDiff ℝ n q) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (fun x : ℝ × ℝ => deriv (fun t => q (x.1, t)) x.2) := by
  unfold deriv
  exact (hq.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).fderiv_apply
    contDiff_snd contDiff_const hmn

private theorem abs_le_mul_sin_of_deriv_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : Differentiable ℝ f) (hzero : f 0 = 0) (hpi : f Real.pi = 0)
    (hM : 0 ≤ M) (hbound : ∀ t ∈ Icc 0 Real.pi, |deriv f t| ≤ M)
    {s : ℝ} (hs : s ∈ Icc 0 Real.pi) :
    |f s| ≤ (M * (Real.pi / 2)) * Real.sin s := by
  have hdist (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
      |f s - f x| ≤ M * |s - x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hf t) (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht)
        (convex_Icc 0 Real.pi) hx hs
  by_cases hhalf : s ≤ Real.pi / 2
  · have hleft : |f s| ≤ M * s := by
      simpa [hzero, abs_of_nonneg hs.1] using
        hdist 0 ⟨le_rfl, Real.pi_pos.le⟩
    have hsine := mul_le_mul_of_nonneg_left (Real.mul_le_sin hs.1 hhalf) Real.pi_pos.le
    have hcancel : Real.pi * (2 / Real.pi * s) = 2 * s := by
      field_simp
    rw [hcancel] at hsine
    have hd : s ≤ (Real.pi / 2) * Real.sin s := by nlinarith
    calc
      |f s| ≤ M * s := hleft
      _ ≤ M * ((Real.pi / 2) * Real.sin s) := mul_le_mul_of_nonneg_left hd hM
      _ = (M * (Real.pi / 2)) * Real.sin s := by ring
  · have hright : |f s| ≤ M * (Real.pi - s) := by
      simpa [hpi, abs_of_nonpos (sub_nonpos.mpr hs.2)] using
        hdist Real.pi ⟨Real.pi_pos.le, le_rfl⟩
    have hsine := mul_le_mul_of_nonneg_left
      (Real.mul_le_sin (sub_nonneg.mpr hs.2) (by linarith : Real.pi - s ≤ Real.pi / 2))
      Real.pi_pos.le
    have hcancel : Real.pi * (2 / Real.pi * (Real.pi - s)) = 2 * (Real.pi - s) := by
      field_simp
    rw [hcancel, Real.sin_pi_sub] at hsine
    have hd : Real.pi - s ≤ (Real.pi / 2) * Real.sin s := by nlinarith
    calc
      |f s| ≤ M * (Real.pi - s) := hright
      _ ≤ M * ((Real.pi / 2) * Real.sin s) := mul_le_mul_of_nonneg_left hd hM
      _ = (M * (Real.pi / 2)) * Real.sin s := by ring

/-- Uniform polar endpoint estimates, including both partial derivatives.
The constant depends on the function and the compact angular interval. -/
theorem exists_pos_polar_endpoint_bounds (q : ℝ × ℝ → ℝ)
    (hq : ContDiff ℝ 2 q) (hzero : ∀ θ, q (0, θ) = 0)
    (hpi : ∀ θ, q (Real.pi, θ) = 0) (a b : ℝ) :
    ∃ C > 0, ∀ s ∈ Icc 0 Real.pi, ∀ θ ∈ Icc a b,
      |q (s, θ)| ≤ C * Real.sin s ∧
      |deriv (fun t => q (t, θ)) s| ≤ C ∧
      |deriv (fun t => q (s, t)) θ| ≤ C * Real.sin s := by
  let g : ℝ × ℝ → ℝ := fun x => deriv (fun t => q (x.1, t)) x.2
  have hg : ContDiff ℝ 1 g := contDiff_deriv_snd hq (by norm_num)
  have hrad : Continuous (fun x : ℝ × ℝ => deriv (fun t => q (t, x.2)) x.1) :=
    (contDiff_deriv_fst hq (m := 1) (by norm_num)).continuous
  have hmix : Continuous (fun x : ℝ × ℝ => deriv (fun t => g (t, x.2)) x.1) :=
    (contDiff_deriv_fst hg (m := 0) (by norm_num)).continuous
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hrad.continuousOn : ContinuousOn _ (Icc 0 Real.pi ×ˢ Icc a b))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hmix.continuousOn : ContinuousOn _ (Icc 0 Real.pi ×ˢ Icc a b))
  let M := |A| + |B| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; linarith [le_abs_self A, abs_nonneg B]
  have hBM : B ≤ M := by dsimp [M]; linarith [le_abs_self B, abs_nonneg A]
  have hrad_bound (s : ℝ) (hs : s ∈ Icc 0 Real.pi) (θ : ℝ) (hθ : θ ∈ Icc a b) :
      |deriv (fun t => q (t, θ)) s| ≤ M := by
    have h := hA (s, θ) ⟨hs, hθ⟩
    exact (by simpa only [Real.norm_eq_abs] using h : |deriv (fun t => q (t, θ)) s| ≤ A).trans hAM
  have hmix_bound (s : ℝ) (hs : s ∈ Icc 0 Real.pi) (θ : ℝ) (hθ : θ ∈ Icc a b) :
      |deriv (fun t => g (t, θ)) s| ≤ M := by
    have h := hB (s, θ) ⟨hs, hθ⟩
    exact (by simpa only [Real.norm_eq_abs] using h : |deriv (fun t => g (t, θ)) s| ≤ B).trans hBM
  have hgzero (θ : ℝ) : g (0, θ) = 0 := by simp [g, hzero]
  have hgpi (θ : ℝ) : g (Real.pi, θ) = 0 := by simp [g, hpi]
  let C := M * (Real.pi / 2 + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; nlinarith [Real.pi_pos]
  have hfactor : M * (Real.pi / 2) ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro s hs θ hθ
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc hs
  have hqdiff : Differentiable ℝ (fun t => q (t, θ)) :=
    (hq.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
  have hgdiff : Differentiable ℝ (fun t => g (t, θ)) :=
    (hg.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
  have hqbound := abs_le_mul_sin_of_deriv_bound hqdiff (hzero θ) (hpi θ) hM.le
    (fun t ht => hrad_bound t ht θ hθ) hs
  have hgbound := abs_le_mul_sin_of_deriv_bound hgdiff (hgzero θ) (hgpi θ) hM.le
    (fun t ht => hmix_bound t ht θ hθ) hs
  exact ⟨hqbound.trans (mul_le_mul_of_nonneg_right hfactor hsin),
    (hrad_bound s hs θ hθ).trans hMC,
    hgbound.trans (mul_le_mul_of_nonneg_right hfactor hsin)⟩

end RicciFlowSharpEstimate.Analysis
