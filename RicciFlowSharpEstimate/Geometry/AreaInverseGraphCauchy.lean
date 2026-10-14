/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaInverseStability
import RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature
import RicciFlowSharpEstimate.Analysis.ParabolicGraphComplete

/-!
# Strong graph Cauchy convergence of actual meridional inverses

Strong curvature and weighted-source convergence force the three canonical
parabolic graph coordinates of actual inverse solutions to be Cauchy. The
sources need only agree with the actual continuous operator on the physical
interval. Raw zero probes and zero sources are included.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem norm_toLp_sq_eq_intervalIntegral (f : ℝ → ℝ)
    (hf : MemLp f 2 areaμ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem dist_toLp_sq_eq_intervalIntegral (f g : ℝ → ℝ)
    (hf : MemLp f 2 areaμ) (hg : MemLp g 2 areaμ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 =
      ∫ x in (0 : ℝ)..1, (f x - g x) ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  exact norm_toLp_sq_eq_intervalIntegral (f - g) (hf.sub hg)

private theorem weighted_norm_toLp_sq (f : ℝ → ℝ)
    (hf : MemLp (fun x => Real.sqrt (x * (1 - x)) * f x) 2 areaμ) :
    ‖hf.toLp (fun x => Real.sqrt (x * (1 - x)) * f x)‖ ^ 2 =
      ∫ x in (0 : ℝ)..1, x * (1 - x) * f x ^ 2 := by
  rw [norm_toLp_sq_eq_intervalIntegral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using hx
  dsimp only
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2))]

private theorem weighted_dist_toLp_sq (f g : ℝ → ℝ)
    (hf : MemLp (fun x => Real.sqrt (x * (1 - x)) * f x) 2 areaμ)
    (hg : MemLp (fun x => Real.sqrt (x * (1 - x)) * g x) 2 areaμ) :
    dist (hf.toLp (fun x => Real.sqrt (x * (1 - x)) * f x))
        (hg.toLp (fun x => Real.sqrt (x * (1 - x)) * g x)) ^ 2 =
      ∫ x in (0 : ℝ)..1, x * (1 - x) * (f x - g x) ^ 2 := by
  rw [dist_toLp_sq_eq_intervalIntegral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using hx
  dsimp only
  rw [← mul_sub, mul_pow, Real.sq_sqrt (mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2))]

private theorem cubic_weighted_dist_toLp_sq (f g : ℝ → ℝ)
    (hf : MemLp (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * f x) 2 areaμ)
    (hg : MemLp (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * g x) 2 areaμ) :
    dist (hf.toLp (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * f x))
        (hg.toLp (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * g x)) ^ 2 =
      ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * (f x - g x) ^ 2 := by
  rw [dist_toLp_sq_eq_intervalIntegral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using hx
  dsimp only
  rw [← mul_sub, mul_pow, mul_pow,
    Real.sq_sqrt (mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2))]
  ring

private theorem cauchySeq_of_dist_sq_le {E : Type*} [PseudoMetricSpace E]
    (v : ℕ → E) (b : ℕ × ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hvb : ∀ n m, dist (v n) (v m) ^ 2 ≤ b (n, m)) : CauchySeq v := by
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have hsq : Tendsto (fun nm : ℕ × ℕ => dist (v nm.1) (v nm.2) ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun nm => hvb nm.1 nm.2) hb
  simpa only [Real.sqrt_sq dist_nonneg, Real.sqrt_zero] using hsq.sqrt

private theorem memLp_weighted_inverse_source (K u g : ℝ → ℝ)
    (hK : Continuous K) (hu : ContDiff ℝ 2 u)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator K u x = g x) :
    MemLp (fun x => Real.sqrt (x * (1 - x)) * g x) 2 areaμ := by
  have hq := meridionalOperator_continuous_of_contDiff_two K u hK hu
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hc : Continuous (fun x => Real.sqrt (x * (1 - x)) * (-meridionalOperator K u x)) :=
    hw.sqrt.mul hq.neg
  have hm : MemLp (fun x => Real.sqrt (x * (1 - x)) * (-meridionalOperator K u x))
      2 areaμ := by
    apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
    exact ((hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  refine (memLp_congr_ae ?_).mp hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [heq x ⟨hx.1.le, hx.2.le⟩]

private theorem deriv_sub_eq_of_contDiff_two (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    deriv (fun x => u x - v x) = (fun x => deriv u x - deriv v x) ∧
      deriv (deriv (fun x => u x - v x)) =
        (fun x => deriv (deriv u) x - deriv (deriv v) x) := by
  have hd : deriv (fun x => u x - v x) = (fun x => deriv u x - deriv v x) := by
    funext x
    exact ((hu.differentiable (by norm_num) x).hasDerivAt.sub
      (hv.differentiable (by norm_num) x).hasDerivAt).deriv
  refine ⟨hd, ?_⟩
  rw [hd]
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  funext x
  exact ((hu1.differentiable (by norm_num) x).hasDerivAt.sub
    (hv1.differentiable (by norm_num) x).hasDerivAt).deriv

/-- Actual inverse equations with strongly converging curvatures and weighted
sources give Cauchy convergence in all three canonical parabolic L² coordinates.
No graph bound, graph Cauchy hypothesis, source continuity, normalization, or
nonzero condition is supplied. The probe jets are their actual derivatives. -/
theorem cauchy_parabolic_graph_of_inverse_sources
    (C : ℝ) (hC : 1 ≤ C) (K u g : ℕ → ℝ → ℝ) (K0 g0 : ℝ → ℝ)
    (hK : ∀ n, IsSmoothAreaCurvature C (K n))
    (hu : ∀ n, ContDiff ℝ 2 (u n))
    (heq : ∀ n x, x ∈ Icc (0 : ℝ) 1 → -meridionalOperator (K n) (u n) x = g n x)
    (hK0 : MemLp K0 2 areaμ)
    (hg0 : MemLp (fun x => Real.sqrt (x * (1 - x)) * g0 x) 2 areaμ)
    (hKL : Tendsto (fun n => eLpNorm (K n - K0) 2 areaμ) atTop (𝓝 0))
    (hgL : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * g n x) -
        (fun x => Real.sqrt (x * (1 - x)) * g0 x)) 2 areaμ) atTop (𝓝 0)) :
    CauchySeq (fun n =>
      ((Analysis.hasParabolicWeakDerivatives_of_contDiff (hu n)).memLp.toLp (u n),
        ((Analysis.hasParabolicWeakDerivatives_of_contDiff (hu n)).memLp_weighted_deriv.toLp
          (fun x => Real.sqrt (x * (1 - x)) * deriv (u n) x),
        (Analysis.hasParabolicWeakDerivatives_of_contDiff (hu n)).memLp_weighted_secondDeriv.toLp
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (u n)) x)))) := by
  let hgraph (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff (hu n)
  let R (n : ℕ) : Lp ℝ 2 areaμ := (hgraph n).memLp.toLp (u n)
  let P (n : ℕ) : Lp ℝ 2 areaμ := (hgraph n).memLp_weighted_deriv.toLp
    (fun x => Real.sqrt (x * (1 - x)) * deriv (u n) x)
  let Z (n : ℕ) : Lp ℝ 2 areaμ := (hgraph n).memLp_weighted_secondDeriv.toLp
    (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (u n)) x)
  have hg (n : ℕ) : MemLp (fun x => Real.sqrt (x * (1 - x)) * g n x) 2 areaμ :=
    memLp_weighted_inverse_source (K n) (u n) (g n) (hK n).1.continuous (hu n) (heq n)
  let F (n : ℕ) : Lp ℝ 2 areaμ :=
    (hg n).toLp (fun x => Real.sqrt (x * (1 - x)) * g n x)
  let A (n : ℕ) : Lp ℝ 2 areaμ := (hK n).memLp_curvature.toLp (K n)
  have hFc : CauchySeq F :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => Real.sqrt (x * (1 - x)) * g n x) hg
      (fun x => Real.sqrt (x * (1 - x)) * g0 x) hg0).mpr hgL).cauchySeq
  have hAc : CauchySeq A :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' K (fun n => (hK n).memLp_curvature)
      K0 hK0).mpr hKL).cauchySeq
  obtain ⟨M, hM, hstab⟩ := exists_uniform_meridional_inverse_stability
    (2 / C) (2 * C) (div_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hC))
  let G (v : ℝ → ℝ) : ℝ := (∫ x in (0 : ℝ)..1, v x ^ 2) +
    (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv v x ^ 2) +
    (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv v) x ^ 2)
  have hGb (n : ℕ) : G (u n) ≤ M * (2 * ‖F n‖ ^ 2) := by
    have hz : ∀ x ∈ Icc (0 : ℝ) 1,
        -meridionalOperator (K n) (fun _ => 0) x = (0 : ℝ) := by
      intro x _
      simp only [meridionalOperator, deriv_const', mul_zero, add_zero, sub_zero, neg_zero]
    have hb := hstab (K n) (K n) (u n) (fun _ => 0) (g n) (fun _ => 0)
      (hK n).1.continuous (hK n).1.continuous (hu n) contDiff_const
      (hK n).common_bounds (hK n).2.2.1 (hK n).2.2.2
      (hK n).2.2.1 (hK n).2.2.2 (heq n) hz
    rw [show ‖F n‖ ^ 2 = ∫ x in (0 : ℝ)..1, x * (1 - x) * g n x ^ 2 from
      weighted_norm_toLp_sq (g n) (hg n)]
    simpa only [G, sub_zero, deriv_const', zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, intervalIntegral.integral_zero, add_zero] using hb
  obtain ⟨D, _, hFD⟩ := cauchySeq_bdd hFc
  let B : ℝ := M * (2 * (D + ‖F 0‖) ^ 2)
  have hGB (n : ℕ) : G (u n) ≤ B := by
    have hn : ‖F n‖ ≤ D + ‖F 0‖ := by
      calc
        ‖F n‖ = dist (F n) 0 := (dist_zero_right _).symm
        _ ≤ dist (F n) (F 0) + dist (F 0) 0 := dist_triangle _ _ _
        _ ≤ D + ‖F 0‖ := by
          simpa only [dist_zero_right] using
            (add_le_add_left (hFD n 0).le (dist (F 0) 0))
    have hn2 : ‖F n‖ ^ 2 ≤ (D + ‖F 0‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact (hGb n).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hn2 (by norm_num)) hM.le)
  have hdist (n m : ℕ) :
      dist (R n) (R m) ^ 2 + dist (P n) (P m) ^ 2 + dist (Z n) (Z m) ^ 2 =
        G (fun x => u n x - u m x) := by
    obtain ⟨hd, hdd⟩ := deriv_sub_eq_of_contDiff_two (u n) (u m) (hu n) (hu m)
    dsimp only [R, P, Z]
    rw [dist_toLp_sq_eq_intervalIntegral, weighted_dist_toLp_sq,
      cubic_weighted_dist_toLp_sq]
    dsimp only [G]
    rw [hdd, hd]
  let b (nm : ℕ × ℕ) : ℝ :=
    M * (2 * dist (F nm.1) (F nm.2) ^ 2 + 120 * B * dist (A nm.1) (A nm.2) ^ 2)
  have hbound (n m : ℕ) :
      dist (R n) (R m) ^ 2 + dist (P n) (P m) ^ 2 + dist (Z n) (Z m) ^ 2 ≤
        b (n, m) := by
    have hb := hstab (K n) (K m) (u n) (u m) (g n) (g m)
      (hK n).1.continuous (hK m).1.continuous (hu n) (hu m)
      (hK n).common_bounds (hK n).2.2.1 (hK n).2.2.2
      (hK m).2.2.1 (hK m).2.2.2 (heq n) (heq m)
    change G (fun x => u n x - u m x) ≤ M *
      (2 * (∫ x in (0 : ℝ)..1, x * (1 - x) * (g n x - g m x) ^ 2) +
        120 * G (u m) * (∫ x in (0 : ℝ)..1, (K n x - K m x) ^ 2)) at hb
    rw [← weighted_dist_toLp_sq (g n) (g m) (hg n) (hg m),
      ← dist_toLp_sq_eq_intervalIntegral (K n) (K m)
        (hK n).memLp_curvature (hK m).memLp_curvature] at hb
    rw [hdist]
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hM.le
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hGB m) (by norm_num)) (sq_nonneg _)
  have hFl : Tendsto (fun nm : ℕ × ℕ => dist (F nm.1) (F nm.2)) atTop (𝓝 0) :=
    cauchySeq_iff_tendsto_dist_atTop_0.mp hFc
  have hAl : Tendsto (fun nm : ℕ × ℕ => dist (A nm.1) (A nm.2)) atTop (𝓝 0) :=
    cauchySeq_iff_tendsto_dist_atTop_0.mp hAc
  have hb : Tendsto b atTop (𝓝 0) := by
    have ht := ((hFl.pow 2).const_mul 2).add ((hAl.pow 2).const_mul (120 * B))
    have ht' := ht.const_mul M
    simpa only [b, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using ht'
  have hRc : CauchySeq R := cauchySeq_of_dist_sq_le R b hb (fun n m => by
    nlinarith only [hbound n m, sq_nonneg (dist (P n) (P m)),
      sq_nonneg (dist (Z n) (Z m))])
  have hPc : CauchySeq P := cauchySeq_of_dist_sq_le P b hb (fun n m => by
    nlinarith only [hbound n m, sq_nonneg (dist (R n) (R m)),
      sq_nonneg (dist (Z n) (Z m))])
  have hZc : CauchySeq Z := cauchySeq_of_dist_sq_le Z b hb (fun n m => by
    nlinarith only [hbound n m, sq_nonneg (dist (R n) (R m)),
      sq_nonneg (dist (P n) (P m))])
  exact hRc.prodMk (hPc.prodMk hZc)

end RicciFlowSharpEstimate.Geometry.AreaProfile
