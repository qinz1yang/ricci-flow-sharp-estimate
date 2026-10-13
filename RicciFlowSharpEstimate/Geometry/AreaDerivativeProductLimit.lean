/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaSublevelGraphBounds
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers
import RicciFlowSharpEstimate.Analysis.L2PointwiseProducts
import Mathlib.Tactic.FieldSimp

/-!
# Weak limits of the derivative part of the area operator

The complete-action sublevel controls the two weighted derivative graph
coordinates. Pointwise convergence of the actual warps and slopes gives
bounded convergent multipliers of these coordinates. This identifies all
L² pairings of the derivative part, without assuming convergence of the
full operator or imposing a boundary condition on the probes.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem derivative_multiplier_bounds {f b w hi : ℝ}
    (hw : 0 < w) (hhi : 0 ≤ hi) (hf : 0 ≤ f ∧ f ≤ hi * w) (hb : |b| ≤ 2) :
    |f * Real.sqrt f / (w * Real.sqrt w)| ≤ hi * Real.sqrt hi ∧
      |2 * b * Real.sqrt f / Real.sqrt w| ≤ 4 * Real.sqrt hi := by
  have hs : Real.sqrt f ≤ Real.sqrt hi * Real.sqrt w := by
    calc
      Real.sqrt f ≤ Real.sqrt (hi * w) := Real.sqrt_le_sqrt hf.2
      _ = Real.sqrt hi * Real.sqrt w := Real.sqrt_mul hhi w
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  constructor
  · rw [abs_of_nonneg (div_nonneg (mul_nonneg hf.1 (Real.sqrt_nonneg f))
      (mul_nonneg hw.le hsw.le))]
    apply (div_le_iff₀ (mul_pos hw hsw)).2
    calc
      f * Real.sqrt f ≤ (hi * w) * (Real.sqrt hi * Real.sqrt w) :=
        mul_le_mul hf.2 hs (Real.sqrt_nonneg f) (mul_nonneg hhi hw.le)
      _ = (hi * Real.sqrt hi) * (w * Real.sqrt w) := by ring
  · rw [abs_div, abs_of_pos hsw]
    apply (div_le_iff₀ hsw).2
    calc
      |2 * b * Real.sqrt f| = 2 * |b| * Real.sqrt f := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (Real.sqrt_nonneg f)]
      _ ≤ (2 * 2) * (Real.sqrt hi * Real.sqrt w) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) hs
          (Real.sqrt_nonneg f) (by norm_num)
      _ = (4 * Real.sqrt hi) * Real.sqrt w := by ring

private theorem derivative_multiplier_cancel {f b w p z : ℝ} (hw : 0 < w) :
    (f * Real.sqrt f / (w * Real.sqrt w)) * (w * Real.sqrt w * z) +
      (2 * b * Real.sqrt f / Real.sqrt w) * (Real.sqrt w * p) =
      Real.sqrt f * (f * z + 2 * b * p) := by
  have hsw : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  field_simp [hw.ne', hsw]

/-- On a normalized complete-action sublevel, pointwise convergence of the
actual primitives and first derivatives, together with weak convergence of
the weighted second derivatives, identifies the weak L² derivative part.
The conclusion includes L² membership of every term and its actual limit. -/
theorem weak_derivative_part_of_area_limits
    (K r : ℕ → ℝ → ℝ) (K0 r0 p0 z0 : ℝ → ℝ) (lo hi B : ℝ)
    (hlo : 0 < lo) (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1)
    (hAction : ∀ n, meridionalAction (K n) (r n) ≤ B)
    (hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ warp (K n) x) atTop (𝓝 (warp K0 x)))
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ warpSlope (K n) x) atTop (𝓝 (warpSlope K0 x)))
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n ↦ deriv (r n) x) atTop (𝓝 (p0 x)))
    (hz : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n ↦ ∫ x,
        (x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x,
          (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) :
    (∀ n, MemLp (fun x ↦ Real.sqrt (warp (K n) x) *
      (warp (K n) x * deriv (deriv (r n)) x +
        2 * warpSlope (K n) x * deriv (r n) x)) 2 areaμ) ∧
    MemLp (fun x ↦ Real.sqrt (warp K0 x) *
      (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) 2 areaμ ∧
    ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n ↦ ∫ x, (Real.sqrt (warp (K n) x) *
        (warp (K n) x * deriv (deriv (r n)) x +
          2 * warpSlope (K n) x * deriv (r n) x)) * v x ∂areaμ)
        atTop (𝓝 (∫ x, (Real.sqrt (warp K0 x) *
          (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) * v x ∂areaμ)) := by
  let w : ℝ → ℝ := fun x ↦ x * (1 - x)
  let f : ℕ → ℝ → ℝ := fun n ↦ warp (K n)
  let b : ℕ → ℝ → ℝ := fun n ↦ warpSlope (K n)
  let f0 : ℝ → ℝ := warp K0
  let b0 : ℝ → ℝ := warpSlope K0
  let Z : ℕ → ℝ → ℝ := fun n x ↦ w x * Real.sqrt (w x) * deriv (deriv (r n)) x
  let Z0 : ℝ → ℝ := fun x ↦ w x * Real.sqrt (w x) * z0 x
  let P : ℕ → ℝ → ℝ := fun n x ↦ Real.sqrt (w x) * deriv (r n) x
  let P0 : ℝ → ℝ := fun x ↦ Real.sqrt (w x) * p0 x
  let a : ℕ → ℝ → ℝ := fun n x ↦ f n x * Real.sqrt (f n x) / (w x * Real.sqrt (w x))
  let a0 : ℝ → ℝ := fun x ↦ f0 x * Real.sqrt (f0 x) / (w x * Real.sqrt (w x))
  let c : ℕ → ℝ → ℝ := fun n x ↦ 2 * b n x * Real.sqrt (f n x) / Real.sqrt (w x)
  let c0 : ℝ → ℝ := fun x ↦ 2 * b0 x * Real.sqrt (f0 x) / Real.sqrt (w x)
  have hhi : 0 ≤ hi :=
    hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans (hbox 0 0 (by norm_num)).2)
  have hwpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < w x := by
    intro x hx
    exact mul_pos hx.1 (sub_pos.mpr hx.2)
  have hwc : Continuous w := by dsimp only [w]; fun_prop
  have hfBounds : ∀ n x, x ∈ Ioo (0 : ℝ) 1 →
      0 ≤ f n x ∧ f n x ≤ hi * w x := by
    intro n x hx
    have hq := warp_bounds_of_curvature_bounds (K n) (hK n) lo hi (hbox n)
      (hzero n) (hone n) x (Ioo_subset_Icc_self hx)
    refine ⟨?_, ?_⟩
    · exact (mul_nonneg hlo.le (hwpos x hx).le).trans
        (by simpa only [f, w, mul_assoc] using hq.1)
    · simpa only [f, w, mul_assoc] using hq.2
  have hbBounds : ∀ n x, x ∈ Ioo (0 : ℝ) 1 → |b n x| ≤ 2 := by
    intro n x hx
    exact abs_warpSlope_le_two (K n) (hK n)
      (fun y hy ↦ hlo.le.trans (hbox n y hy).1) (hzero n) x (Ioo_subset_Icc_self hx)
  have hf0Bounds : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f0 x ∧ f0 x ≤ hi * w x := by
    intro x hx
    exact ⟨ge_of_tendsto' (hf x hx) (fun n ↦ (hfBounds n x hx).1),
      le_of_tendsto' (hf x hx) (fun n ↦ (hfBounds n x hx).2)⟩
  have hb0Bounds : ∀ x ∈ Ioo (0 : ℝ) 1, |b0 x| ≤ 2 := by
    intro x hx
    exact le_of_tendsto' (hb x hx).abs (fun n ↦ hbBounds n x hx)
  have hfAE : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ f n x) atTop (𝓝 (f0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hf x hx
  have hbAE : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ b n x) atTop (𝓝 (b0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hb x hx
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) areaμ := fun n ↦
    (warp_continuous (K n) (hK n)).aestronglyMeasurable
  have hbmeas : ∀ n, AEStronglyMeasurable (b n) areaμ := fun n ↦
    (warpSlope_continuous (K n) (hK n)).aestronglyMeasurable
  have hf0meas : AEStronglyMeasurable f0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hfmeas hfAE
  have hb0meas : AEStronglyMeasurable b0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hbmeas hbAE
  have hsfmeas : ∀ n, AEStronglyMeasurable (fun x ↦ Real.sqrt (f n x)) areaμ :=
    fun n ↦ Real.continuous_sqrt.comp_aestronglyMeasurable (hfmeas n)
  have hsf0meas : AEStronglyMeasurable (fun x ↦ Real.sqrt (f0 x)) areaμ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf0meas
  have hameas : ∀ n, AEStronglyMeasurable (a n) areaμ := by
    intro n
    exact (((hfmeas n).mul (hsfmeas n)).aemeasurable.div
      (hwc.mul hwc.sqrt).aemeasurable).aestronglyMeasurable
  have ha0meas : AEStronglyMeasurable a0 areaμ :=
    ((hf0meas.mul hsf0meas).aemeasurable.div
      (hwc.mul hwc.sqrt).aemeasurable).aestronglyMeasurable
  have hcmeas : ∀ n, AEStronglyMeasurable (c n) areaμ := by
    intro n
    exact ((((hbmeas n).const_mul 2).mul (hsfmeas n)).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have hc0meas : AEStronglyMeasurable c0 areaμ :=
    (((hb0meas.const_mul 2).mul hsf0meas).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have haBound : ∀ n, ∀ᵐ x ∂areaμ, |a n x| ≤ hi * Real.sqrt hi := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (derivative_multiplier_bounds (hwpos x hx) hhi (hfBounds n x hx)
      (hbBounds n x hx)).1
  have ha0Bound : ∀ᵐ x ∂areaμ, |a0 x| ≤ hi * Real.sqrt hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (derivative_multiplier_bounds (hwpos x hx) hhi (hf0Bounds x hx)
      (hb0Bounds x hx)).1
  have hcBound : ∀ n, ∀ᵐ x ∂areaμ, |c n x| ≤ 4 * Real.sqrt hi := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (derivative_multiplier_bounds (hwpos x hx) hhi (hfBounds n x hx)
      (hbBounds n x hx)).2
  have hc0Bound : ∀ᵐ x ∂areaμ, |c0 x| ≤ 4 * Real.sqrt hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (derivative_multiplier_bounds (hwpos x hx) hhi (hf0Bounds x hx)
      (hb0Bounds x hx)).2
  have haConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ a n x) atTop (𝓝 (a0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hf x hx).mul (hf x hx).sqrt).div_const (w x * Real.sqrt (w x))
  have hcConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ c n x) atTop (𝓝 (c0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (((hb x hx).const_mul 2).mul (hf x hx).sqrt).div_const (Real.sqrt (w x))
  obtain ⟨M, _, hM⟩ := exists_uniform_parabolic_graph_bound lo hi hlo hhi B
  have hbound (n : ℕ) := hM (K n) (r n) (hK n) (hr n) (hbox n)
    (hzero n) (hone n) (hmass n) (hAction n)
  have hZ : ∀ n, MemLp (Z n) 2 areaμ := fun n ↦
    (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)).memLp_weighted_secondDeriv
  have hZ0 : MemLp Z0 2 areaμ := hgraph.memLp_weighted_secondDeriv
  have hP : ∀ n, MemLp (P n) 2 areaμ := fun n ↦
    (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)).memLp_weighted_deriv
  have hP0 : MemLp P0 2 areaμ := hgraph.memLp_weighted_deriv
  have hPConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ P n x) atTop (𝓝 (P0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hp x hx).const_mul (Real.sqrt (w x))
  have hPweak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n ↦ ∫ x, P n x * v x ∂areaμ) atTop (𝓝 (∫ x, P0 x * v x ∂areaμ)) :=
    fun v ↦ Analysis.tendsto_integral_mul_of_ae_tendsto_of_integral_sq_bound
      hP (Lp.memLp v) M (fun n ↦ (hbound n).2.1) hPConv
  have hAZ := Analysis.weak_L2_mul_of_ae_tendsto_of_ae_abs_le
    hZ hZ0 (fun n ↦ (hbound n).2.2) hz hameas ha0meas haBound ha0Bound haConv
  have hCP := Analysis.weak_L2_mul_of_ae_tendsto_of_ae_abs_le
    hP hP0 (fun n ↦ (hbound n).2.1) hPweak hcmeas hc0meas hcBound hc0Bound hcConv
  have hEq (n : ℕ) :
      (fun x ↦ a n x * Z n x + c n x * P n x) =ᵐ[areaμ]
        (fun x ↦ Real.sqrt (warp (K n) x) *
          (warp (K n) x * deriv (deriv (r n)) x +
            2 * warpSlope (K n) x * deriv (r n) x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact derivative_multiplier_cancel (hwpos x hx)
  have hEq0 : (fun x ↦ a0 x * Z0 x + c0 x * P0 x) =ᵐ[areaμ]
      (fun x ↦ Real.sqrt (warp K0 x) *
        (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact derivative_multiplier_cancel (hwpos x hx)
  refine ⟨fun n ↦ ((hAZ.1 n).add (hCP.1 n)).ae_eq (hEq n),
    (hAZ.2.1.add hCP.2.1).ae_eq hEq0, ?_⟩
  intro v
  have hpair (n : ℕ) :
      (∫ x, (Real.sqrt (warp (K n) x) *
        (warp (K n) x * deriv (deriv (r n)) x +
          2 * warpSlope (K n) x * deriv (r n) x)) * v x ∂areaμ) =
      (∫ x, (a n x * Z n x) * v x ∂areaμ) +
        ∫ x, (c n x * P n x) * v x ∂areaμ := by
    have hiA : Integrable (fun x => (a n x * Z n x) * v x) areaμ :=
      (hAZ.1 n).integrable_mul (Lp.memLp v)
    have hiC : Integrable (fun x => (c n x * P n x) * v x) areaμ :=
      (hCP.1 n).integrable_mul (Lp.memLp v)
    rw [← integral_add hiA hiC]
    apply integral_congr_ae
    filter_upwards [hEq n] with x hx
    rw [← hx, add_mul]
  have hpair0 :
      (∫ x, (Real.sqrt (warp K0 x) *
        (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) * v x ∂areaμ) =
      (∫ x, (a0 x * Z0 x) * v x ∂areaμ) +
        ∫ x, (c0 x * P0 x) * v x ∂areaμ := by
    have hiA : Integrable (fun x => (a0 x * Z0 x) * v x) areaμ :=
      hAZ.2.1.integrable_mul (Lp.memLp v)
    have hiC : Integrable (fun x => (c0 x * P0 x) * v x) areaμ :=
      hCP.2.1.integrable_mul (Lp.memLp v)
    rw [← integral_add hiA hiC]
    apply integral_congr_ae
    filter_upwards [hEq0] with x hx
    rw [← hx, add_mul]
  simpa only [hpair, hpair0] using (hAZ.2.2 v).add (hCP.2.2 v)

end RicciFlowSharpEstimate.Geometry.AreaProfile
