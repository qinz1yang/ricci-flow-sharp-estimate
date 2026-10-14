/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaGreenQuotientRegularity
import RicciFlowSharpEstimate.Geometry.AreaProbeMaximumPrinciple
import RicciFlowSharpEstimate.Geometry.AreaActionVariation
import RicciFlowSharpEstimate.Analysis.SmoothIntervalExtension
import RicciFlowSharpEstimate.Analysis.ClosedIntervalDerivatives
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.ProjIcc

/-!
# Smooth inversion of the physical meridional operator

The Green quotient has exact curvature row mass one half. This gives an
actual contraction on continuous functions on the physical interval. Its
fixed point gains every finite derivative through the two poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter
open scoped ContDiff Topology NNReal

private theorem inverse_weighted_curvature_moment (K : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1) :
    (∫ t in (0 : ℝ)..1, (1 - t) * K t) = 1 := by
  have hKI : IntervalIntegrable (fun t : ℝ => t * K t) volume 0 1 :=
    (continuous_id.mul hK).intervalIntegrable 0 1
  calc
    _ = ∫ t in (0 : ℝ)..1, K t - t * K t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = 1 := by
      rw [intervalIntegral.integral_sub (hK.intervalIntegrable 0 1) hKI, hzero, hone]
      norm_num

private theorem inverse_warp_green (K : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp K x = 2 * ∫ t in (0 : ℝ)..1, Analysis.unitDirichletKernel x t * K t := by
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hK.intervalIntegrable 0 1)
  rw [Analysis.integral_unitDirichletKernel K hKi x hx,
    inverse_weighted_curvature_moment K hK hzero hone]
  simp only [warp, mul_one]
  ring

private theorem inverse_quotient_curvature (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : areaGreenQuotient K K x = 1 / 2 := by
  by_cases hx0 : x = 0
  · subst x
    simp [areaGreenQuotient, inverse_weighted_curvature_moment K hK hzero hone]
  by_cases hx1 : x = 1
  · subst x
    simp [areaGreenQuotient, hone]
  have hxi : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have hf := warp_pos_of_moments K hK hpos hzero hone x hxi
  have hw := inverse_warp_green K hK hzero hone x hx
  simp only [areaGreenQuotient, ite_eq_right hx0, ite_eq_right hx1]
  apply (div_eq_iff hf.ne').mpr
  linarith

private theorem inverse_kernel_nonneg (x t : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ Analysis.unitDirichletKernel x t := by
  by_cases htx : t ≤ x
  · rw [Analysis.unitDirichletKernel, min_eq_right htx]
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hx.2)]
  · rw [Analysis.unitDirichletKernel, min_eq_left (le_of_not_ge htx)]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr ht.2)]

private theorem inverse_weighted_integral_bound (w h l K : ℝ → ℝ) (C : ℝ)
    (hw : Continuous w) (hh : Continuous h) (hl : Continuous l) (hK : Continuous K)
    (hwpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |h t - l t| ≤ C * K t) :
    |(∫ t in (0 : ℝ)..1, w t * h t) - ∫ t in (0 : ℝ)..1, w t * l t| ≤
      C * ∫ t in (0 : ℝ)..1, w t * K t := by
  have hWH : IntervalIntegrable (fun t => w t * h t) volume 0 1 :=
    (hw.mul hh).intervalIntegrable 0 1
  have hWL : IntervalIntegrable (fun t => w t * l t) volume 0 1 :=
    (hw.mul hl).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hWH hWL]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |w t * h t - w t * l t| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, C * (w t * K t) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (((hw.mul hh).sub (hw.mul hl)).abs.intervalIntegrable 0 1)
        ((continuous_const.mul (hw.mul hK)).intervalIntegrable 0 1)
      intro t ht
      change |w t * h t - w t * l t| ≤ C * (w t * K t)
      rw [← mul_sub, abs_mul, abs_of_nonneg (hwpos t ht)]
      nlinarith [mul_le_mul_of_nonneg_left (hbound t ht) (hwpos t ht)]
    _ = C * ∫ t in (0 : ℝ)..1, w t * K t :=
      intervalIntegral.integral_const_mul C (fun t => w t * K t)

private theorem inverse_quotient_abs_sub_le (K h l : ℝ → ℝ) (C : ℝ)
    (hK : Continuous K) (hh : Continuous h) (hl : Continuous l)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |h t - l t| ≤ C * K t)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |areaGreenQuotient K h x - areaGreenQuotient K l x| ≤ C / 2 := by
  have hrow : |areaGreenQuotient K h x - areaGreenQuotient K l x| ≤
      C * areaGreenQuotient K K x := by
    by_cases hx0 : x = 0
    · subst x
      simp only [areaGreenQuotient, ite_true]
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := inverse_weighted_integral_bound (fun t => 1 - t) h l K C
        (continuous_const.sub continuous_id) hh hl hK
        (fun t ht => sub_nonneg.mpr ht.2) hbound
      calc
        _ ≤ (C * ∫ t in (0 : ℝ)..1, (1 - t) * K t) / 2 := by
          exact div_le_div_of_nonneg_right hb (by norm_num)
        _ = _ := by ring
    by_cases hx1 : x = 1
    · subst x
      simp only [areaGreenQuotient, one_ne_zero, ite_false, ite_true]
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := inverse_weighted_integral_bound (fun t => t) h l K C
        continuous_id hh hl hK (fun t ht => ht.1) hbound
      calc
        _ ≤ (C * ∫ t in (0 : ℝ)..1, t * K t) / 2 := by
          exact div_le_div_of_nonneg_right hb (by norm_num)
        _ = _ := by ring
    have hxi : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hf := warp_pos_of_moments K hK hpos hzero hone x hxi
    simp only [areaGreenQuotient, ite_eq_right hx0, ite_eq_right hx1]
    rw [← sub_div, abs_div, abs_of_pos hf]
    have hw : Continuous (fun t => Analysis.unitDirichletKernel x t) := by
      unfold Analysis.unitDirichletKernel
      fun_prop
    have hb := inverse_weighted_integral_bound
      (fun t => Analysis.unitDirichletKernel x t) h l K C hw hh hl hK
      (fun t ht => inverse_kernel_nonneg x t hx ht) hbound
    calc
      _ ≤ (C * ∫ t in (0 : ℝ)..1, Analysis.unitDirichletKernel x t * K t) /
          warp K x := div_le_div_of_nonneg_right hb hf.le
      _ = _ := by ring
  rw [inverse_quotient_curvature K hK hpos hzero hone x hx] at hrow
  linarith

private theorem inverse_exists_continuous_fixedPoint (K g : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hg : Continuous g)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1) :
    ∃ u : ℝ → ℝ, Continuous u ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      u x = areaGreenQuotient K (fun t => g t + K t * u t) x := by
  let U := C(Icc (0 : ℝ) 1, ℝ)
  have hsrc (u : U) : Continuous (fun t => g t + K t * IccExtend zero_le_one u t) :=
    hg.add (hK.continuous.mul (continuous_IccExtend_iff.mpr u.continuous))
  let A : U → U := fun u =>
    ⟨fun x => areaGreenQuotient K (fun t => g t + K t * IccExtend zero_le_one u t) x,
      continuousOn_iff_continuous_domRestrict.mp
        (areaGreenQuotient_contDiffOn_succ 0 K
          (fun t => g t + K t * IccExtend zero_le_one u t) hK hpos hzero hone
          (contDiffOn_zero.mpr (hsrc u).continuousOn)).continuousOn⟩
  have hLip : LipschitzWith (1 / 2 : ℝ≥0) A := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (A u) (A v) ≤ (1 / 2 : ℝ) * dist u v
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro x
    have hb : ∀ t ∈ Icc (0 : ℝ) 1,
        |(g t + K t * IccExtend zero_le_one u t) -
          (g t + K t * IccExtend zero_le_one v t)| ≤ dist u v * K t := by
      intro t ht
      rw [IccExtend_of_mem zero_le_one u ht, IccExtend_of_mem zero_le_one v ht]
      have hd := ContinuousMap.dist_apply_le_dist (f := u) (g := v) ⟨t, ht⟩
      rw [Real.dist_eq] at hd
      have heq : (g t + K t * u ⟨t, ht⟩) - (g t + K t * v ⟨t, ht⟩) =
          K t * (u ⟨t, ht⟩ - v ⟨t, ht⟩) := by ring
      rw [heq, abs_mul, abs_of_pos (hpos t ht)]
      nlinarith [mul_le_mul_of_nonneg_left hd (hpos t ht).le]
    have h := inverse_quotient_abs_sub_le K
      (fun t => g t + K t * IccExtend zero_le_one u t)
      (fun t => g t + K t * IccExtend zero_le_one v t) (dist u v)
      hK.continuous (hsrc u) (hsrc v) hpos hzero hone hb x x.property
    change dist
      (areaGreenQuotient K (fun t => g t + K t * IccExtend zero_le_one u t) x)
      (areaGreenQuotient K (fun t => g t + K t * IccExtend zero_le_one v t) x) ≤ _
    rw [Real.dist_eq]
    linarith
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) A := ⟨by norm_num, hLip⟩
  let u : U := hcontract.fixedPoint A
  have hfix : A u = u := hcontract.fixedPoint_isFixedPt
  refine ⟨IccExtend zero_le_one u,
    continuous_IccExtend_iff.mpr u.continuous, ?_⟩
  intro x hx
  have h := congrArg (fun v : U => v ⟨x, hx⟩) hfix
  change areaGreenQuotient K
    (fun t => g t + K t * IccExtend zero_le_one u t) x = u ⟨x, hx⟩ at h
  rw [IccExtend_of_mem zero_le_one u hx]
  exact h.symm

private theorem inverse_fixedPoint_contDiffOn (K g u : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hg : ContDiff ℝ ∞ g) (hu : Continuous u)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1)
    (hfix : ∀ x ∈ Icc (0 : ℝ) 1,
      u x = areaGreenQuotient K (fun t => g t + K t * u t) x) :
    ContDiffOn ℝ ∞ u (Icc (0 : ℝ) 1) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hu.continuousOn
  | succ n ih =>
      have hsource : ContDiffOn ℝ n (fun t => g t + K t * u t) (Icc (0 : ℝ) 1) :=
        (hg.of_le (by simp)).contDiffOn.add ((hK.of_le (by simp)).contDiffOn.mul ih)
      exact (areaGreenQuotient_contDiffOn_succ n K _ hK hpos hzero hone hsource).congr hfix

private theorem inverse_quotient_congr (K h l : ℝ → ℝ)
    (heq : EqOn h l (Icc (0 : ℝ) 1)) (x : ℝ) :
    areaGreenQuotient K h x = areaGreenQuotient K l x := by
  have hi (w : ℝ → ℝ) : (∫ t in (0 : ℝ)..1, w t * h t) =
      ∫ t in (0 : ℝ)..1, w t * l t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [heq ht']
  unfold areaGreenQuotient
  rw [hi (fun t => 1 - t), hi (fun t => t), hi (fun t => Analysis.unitDirichletKernel x t)]

private theorem inverse_primitive_second (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    deriv (deriv (Analysis.unitDirichletPrimitive h)) x = -h x := by
  have hd : deriv (Analysis.unitDirichletPrimitive h) =
      fun y => (∫ t in (0 : ℝ)..1, (1 - t) * h t) - ∫ t in (0 : ℝ)..y, h t := by
    funext y
    exact (Analysis.unitDirichletPrimitive_hasDerivAt h hh y).deriv
  rw [hd]
  exact ((hh.integral_hasStrictDerivAt 0 x).hasDerivAt.const_sub
    (∫ t in (0 : ℝ)..1, (1 - t) * h t)).deriv

private theorem inverse_product_second (K u : ℝ → ℝ) (hK : Continuous K)
    (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    deriv (deriv (fun y => warp K y * u y)) x =
      meridionalOperator K u x - K x * u x := by
  have hu1 : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hd : deriv (fun y => warp K y * u y) =
      fun y => warpSlope K y * u y + warp K y * deriv u y := by
    funext y
    exact ((warp_hasDerivAt K hK y).mul (hu.differentiable (by simp) y).hasDerivAt).deriv
  rw [hd]
  calc
    _ = ((-2 * K x) * u x + warpSlope K x * deriv u x) +
        (warpSlope K x * deriv u x + warp K x * deriv (deriv u) x) := by
      exact (((warpSlope_hasDerivAt K hK x).mul
        (hu.differentiable (by simp) x).hasDerivAt).add
        ((warp_hasDerivAt K hK x).mul
          (hu1.differentiable (by simp) x).hasDerivAt)).deriv
    _ = _ := by
      unfold meridionalOperator
      ring

private theorem inverse_exists_smooth_solution (K g : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      ∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator K u x = g x := by
  obtain ⟨v, hv, hfix⟩ :=
    inverse_exists_continuous_fixedPoint K g hK hg.continuous hpos hzero hone
  have hvSmooth := inverse_fixedPoint_contDiffOn K g v hK hg hv hpos hzero hone hfix
  obtain ⟨u, hu, hEq⟩ := Analysis.exists_contDiff_extension_Icc v 0 1 zero_lt_one hvSmooth
  let H : ℝ → ℝ := fun t => g t + K t * u t
  have hH : ContDiff ℝ ∞ H := hg.add (hK.mul hu)
  have hufix : ∀ x ∈ Icc (0 : ℝ) 1, u x = areaGreenQuotient K H x := by
    intro x hx
    calc
      u x = v x := hEq hx
      _ = areaGreenQuotient K (fun t => g t + K t * v t) x := hfix x hx
      _ = areaGreenQuotient K H x := by
        apply inverse_quotient_congr
        intro t ht
        dsimp only [H]
        rw [hEq ht]
  have hHInt : IntegrableOn H (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hH.continuous.intervalIntegrable 0 1)
  have hprod : EqOn (fun x => warp K x * u x)
      (Analysis.unitDirichletPrimitive H) (Icc (0 : ℝ) 1) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [warp_zero, zero_mul, Analysis.unitDirichletPrimitive_zero]
    by_cases hx1 : x = 1
    · subst x
      dsimp only
      rw [warp_one K hK.continuous hzero hone]
      simp only [zero_mul, Analysis.unitDirichletPrimitive_one]
    have hxi : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hf := warp_pos_of_moments K hK.continuous hpos hzero hone x hxi
    have hval := hufix x hx
    simp only [areaGreenQuotient, ite_eq_right hx0, ite_eq_right hx1] at hval
    rw [Analysis.unitDirichletPrimitive_eq_integral H hHInt x hx]
    calc
      warp K x * u x = u x * warp K x := mul_comm _ _
      _ = _ := (eq_div_iff hf.ne').mp hval
  have hp2 : ContDiff ℝ 2 (Analysis.unitDirichletPrimitive H) :=
    Analysis.unitDirichletPrimitive_contDiff 0 H (hH.of_le (by simp))
  have hderiv := (Analysis.eqOn_derivatives_Icc 0 1 zero_lt_one
    (fun x => warp K x * u x) (Analysis.unitDirichletPrimitive H)
    (((warp_contDiff K hK).mul hu).of_le (by simp)) hp2 hprod).2
  refine ⟨u, hu, ?_⟩
  intro x hx
  have h := hderiv hx
  rw [inverse_product_second K u hK.continuous hu x,
    inverse_primitive_second H hH.continuous x] at h
  dsimp only [H] at h
  linarith

/-- Every smooth source has a globally smooth physical meridional inverse.
The solution is unique on the closed physical interval and is nonnegative
there whenever its source is nonnegative. No probe pole values are imposed,
and the source may be identically zero. -/
theorem exists_smooth_meridional_inverse (K g : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ t in (0 : ℝ)..1, K t) = 2)
    (hone : (∫ t in (0 : ℝ)..1, t * K t) = 1) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator K u x = g x) ∧
      ((∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x) → ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ u x) ∧
      (∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
        (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator K v x = g x) →
        EqOn v u (Icc (0 : ℝ) 1)) := by
  obtain ⟨u, hu, hsolve⟩ := inverse_exists_smooth_solution K g hK hg hpos hzero hone
  refine ⟨u, hu, hsolve, ?_, ?_⟩
  · intro hgpos
    apply nonneg_of_meridionalOperator_nonpos K u hK.continuous hpos
      (hu.of_le (by simp)) hzero hone
    intro x hx
    linarith [hsolve x hx, hgpos x hx]
  · intro v hv hvsolve
    have hvu : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ v x + (-1) * u x := by
      apply nonneg_of_meridionalOperator_nonpos K (fun x => v x + (-1) * u x)
        hK.continuous hpos ((hv.add (contDiff_const.mul hu)).of_le (by simp)) hzero hone
      intro x hx
      rw [meridionalOperator_add_mul K v u hv hu (-1) x]
      linarith [hvsolve x hx, hsolve x hx]
    have huv : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ u x + (-1) * v x := by
      apply nonneg_of_meridionalOperator_nonpos K (fun x => u x + (-1) * v x)
        hK.continuous hpos ((hu.add (contDiff_const.mul hv)).of_le (by simp)) hzero hone
      intro x hx
      rw [meridionalOperator_add_mul K u v hu hv (-1) x]
      linarith [hvsolve x hx, hsolve x hx]
    intro x hx
    linarith [hvu x hx, huv x hx]

end RicciFlowSharpEstimate.Geometry.AreaProfile
