/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaInverseEstimate
import RicciFlowSharpEstimate.Geometry.AreaOperatorStability

/-!
# Uniform stability for actual meridional inverse solutions

The graph difference of two probes is controlled by their actual source
difference and the curvature difference. The curvature error acts on the
same second probe, so a uniform graph bound gives a two-index Cauchy estimate.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

private theorem meridionalOperator_sub_of_contDiff_two (K u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : ℝ) :
    meridionalOperator K (fun y => u y - v y) x =
      meridionalOperator K u x - meridionalOperator K v x := by
  have hd : deriv (fun y => u y - v y) = fun y => deriv u y - deriv v y := by
    funext y
    exact ((hu.differentiable (by norm_num) y).hasDerivAt.sub
      (hv.differentiable (by norm_num) y).hasDerivAt).deriv
  have hdd : deriv (deriv (fun y => u y - v y)) =
      fun y => deriv (deriv u) y - deriv (deriv v) y := by
    rw [hd]
    have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
    have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
    funext y
    exact ((hu1.differentiable (by norm_num) y).hasDerivAt.sub
      (hv1.differentiable (by norm_num) y).hasDerivAt).deriv
  unfold meridionalOperator
  rw [hdd, hd]
  ring

/-- Two actual inverse equations have a uniform asymmetric graph stability
estimate controlled by the first curvature's positive box. Both curvatures
have the same normalized moments. The sources may vanish, and neither probe
is mass-normalized. The constant depends only on the first curvature box. -/
theorem exists_uniform_meridional_inverse_stability (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ M > (0 : ℝ), ∀ K L u v g h : ℝ → ℝ,
      Continuous K → Continuous L → ContDiff ℝ 2 u → ContDiff ℝ 2 v →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      (∫ x in (0 : ℝ)..1, L x) = 2 → (∫ x in (0 : ℝ)..1, x * L x) = 1 →
      (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator K u x = g x) →
      (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator L v x = h x) →
      (∫ x in (0 : ℝ)..1, (u x - v x) ^ 2) +
        (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv (fun y => u y - v y) x ^ 2) +
        (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 *
          deriv (deriv (fun y => u y - v y)) x ^ 2) ≤
        M * (2 * (∫ x in (0 : ℝ)..1, x * (1 - x) * (g x - h x) ^ 2) +
          120 * ((∫ x in (0 : ℝ)..1, v x ^ 2) +
            (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv v x ^ 2) +
            (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv v) x ^ 2)) *
              (∫ x in (0 : ℝ)..1, (K x - L x) ^ 2)) := by
  obtain ⟨D, hD, hgraph⟩ := exists_uniform_meridional_inverse_graph_bound lo hi hlo
  refine ⟨D * (|hi| + 1), mul_pos hD (by positivity), ?_⟩
  intro K L u v g h hK hL hu hv hKbox hKzero hKone hLzero hLone hsourceu hsourcev
  let w : ℝ → ℝ := fun x => x * (1 - x)
  let d : ℝ → ℝ := fun x => u x - v x
  let S := ∫ x in (0 : ℝ)..1, w x * (g x - h x) ^ 2
  let T := (∫ x in (0 : ℝ)..1, v x ^ 2) +
    (∫ x in (0 : ℝ)..1, w x * deriv v x ^ 2) +
    (∫ x in (0 : ℝ)..1, w x ^ 3 * deriv (deriv v) x ^ 2)
  let E := ∫ x in (0 : ℝ)..1, (K x - L x) ^ 2
  have hd : ContDiff ℝ 2 d := hu.sub hv
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hqu := meridionalOperator_continuous_of_contDiff_two K u hK hu
  have hqv := meridionalOperator_continuous_of_contDiff_two K v hK hv
  have hqLv := meridionalOperator_continuous_of_contDiff_two L v hL hv
  have hqd := meridionalOperator_continuous_of_contDiff_two K d hK hd
  have hsourceEq :
      (∫ x in (0 : ℝ)..1, w x * (meridionalOperator K u x - meridionalOperator L v x) ^ 2) = S := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using hx
    have huEq : meridionalOperator K u x = -g x := by linarith only [hsourceu x hx']
    have hvEq : meridionalOperator L v x = -h x := by linarith only [hsourcev x hx']
    dsimp only
    rw [huEq, hvEq]
    ring
  have hsourceC : Continuous (fun x =>
      w x * (meridionalOperator K u x - meridionalOperator L v x) ^ 2) := by fun_prop
  have herrorC : Continuous (fun x =>
      w x * (meridionalOperator K v x - meridionalOperator L v x) ^ 2) := by fun_prop
  have hopC : Continuous (fun x => w x * meridionalOperator K d x ^ 2) := by fun_prop
  have hsplit : (∫ x in (0 : ℝ)..1, w x * meridionalOperator K d x ^ 2) ≤
      ∫ x in (0 : ℝ)..1,
        2 * (w x * (meridionalOperator K u x - meridionalOperator L v x) ^ 2) +
        2 * (w x * (meridionalOperator K v x - meridionalOperator L v x) ^ 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one (hopC.intervalIntegrable 0 1)
      (((hsourceC.const_mul 2).add (herrorC.const_mul 2)).intervalIntegrable 0 1)
    intro x hx
    have hlin : meridionalOperator K d x =
        meridionalOperator K u x - meridionalOperator K v x :=
      meridionalOperator_sub_of_contDiff_two K u v hu hv x
    have hsq : meridionalOperator K d x ^ 2 ≤
        2 * (meridionalOperator K u x - meridionalOperator L v x) ^ 2 +
        2 * (meridionalOperator K v x - meridionalOperator L v x) ^ 2 := by
      rw [hlin]
      nlinarith only [sq_nonneg (meridionalOperator K u x +
        meridionalOperator K v x - 2 * meridionalOperator L v x)]
    have hscaled := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))
    change x * (1 - x) * _ ≤ _
    dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, w] at hscaled ⊢
    nlinarith only [hscaled]
  rw [intervalIntegral.integral_add ((hsourceC.const_mul 2).intervalIntegrable 0 1)
      ((herrorC.const_mul 2).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsourceEq] at hsplit
  have hvariation := meridionalOperator_sub_curvature_energy_le K L v hK hL hv
    (hKzero.trans hLzero.symm) (hKone.trans hLone.symm)
  change (∫ x in (0 : ℝ)..1,
    w x * (meridionalOperator K v x - meridionalOperator L v x) ^ 2) ≤ 60 * T * E at hvariation
  have hoperator : (∫ x in (0 : ℝ)..1, w x * meridionalOperator K d x ^ 2) ≤
      2 * S + 120 * T * E := by
    nlinarith only [hsplit, hvariation]
  have henergy : probeOperatorEnergy K d ≤
      hi * (∫ x in (0 : ℝ)..1, w x * meridionalOperator K d x ^ 2) := by
    unfold probeOperatorEnergy
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      (((warp_continuous K hK).mul (hqd.pow 2)).intervalIntegrable 0 1)
      ((hopC.const_mul hi).intervalIntegrable 0 1)
    intro x hx
    have hf := (warp_bounds_of_curvature_bounds K hK lo hi hKbox hKzero hKone x hx).2
    have hscaled := mul_le_mul_of_nonneg_right hf (sq_nonneg (meridionalOperator K d x))
    dsimp only [Pi.mul_apply, Pi.pow_apply, w] at hscaled ⊢
    nlinarith only [hscaled]
  have hhi : 0 ≤ hi := (hlo.le.trans (hKbox 0 (by norm_num)).1).trans (hKbox 0 (by norm_num)).2
  have henergy' : probeOperatorEnergy K d ≤ hi * (2 * S + 120 * T * E) :=
    henergy.trans (mul_le_mul_of_nonneg_left hoperator hhi)
  have hS0 : 0 ≤ S := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (sq_nonneg _)
  have hE0 : 0 ≤ E :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (K x - L x))
  have hT0 : 0 ≤ T := by
    apply add_nonneg
    · apply add_nonneg
      · exact intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (v x))
      · apply intervalIntegral.integral_nonneg zero_le_one
        intro x hx
        exact mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (sq_nonneg _)
    · apply intervalIntegral.integral_nonneg zero_le_one
      intro x hx
      exact mul_nonneg (pow_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) 3) (sq_nonneg _)
  have hmajor : hi ≤ |hi| + 1 := by linarith only [le_abs_self hi]
  have henergy'' : probeOperatorEnergy K d ≤ (|hi| + 1) * (2 * S + 120 * T * E) :=
    henergy'.trans (mul_le_mul_of_nonneg_right hmajor (by positivity))
  have hbound := hgraph K d hK hd hKbox hKzero hKone
  have hscaled := mul_le_mul_of_nonneg_left henergy'' hD.le
  change (∫ x in (0 : ℝ)..1, d x ^ 2) +
    (∫ x in (0 : ℝ)..1, w x * deriv d x ^ 2) +
    (∫ x in (0 : ℝ)..1, w x ^ 3 * deriv (deriv d) x ^ 2) ≤
      D * (|hi| + 1) * (2 * S + 120 * T * E)
  nlinarith only [hbound, hscaled]

end RicciFlowSharpEstimate.Geometry.AreaProfile
