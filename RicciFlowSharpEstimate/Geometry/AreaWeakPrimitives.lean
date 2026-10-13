/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfile
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pointwise area primitives under weak L2 curvature convergence

The original warping slope and warping coefficient are identified by the
L2 tests `1_(0,x)` and `(x-s) 1_(0,x)`. Restriction of the measure and removal
of the null right endpoint identify these pairings with the original
interval-integral definitions, including both normalized endpoints.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set

local notation "μ₀" => (volume.restrict (Ioo (0 : ℝ) 1))

private theorem integral_mul_toLp_indicator_eq_intervalIntegral
    (K q : ℝ → ℝ) (hK : MemLp K 2 μ₀) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hq : MemLp ((Ioo (0 : ℝ) x).indicator q) 2 μ₀) :
    (∫ s, K s * (hq.toLp ((Ioo (0 : ℝ) x).indicator q)) s ∂μ₀) =
      ∫ s in (0 : ℝ)..x, q s * K s := by
  calc
    _ = inner ℝ (hK.toLp K) (hq.toLp ((Ioo (0 : ℝ) x).indicator q)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK.coeFn_toLp] with s hs
      simp only [Real.inner_apply, hs]
    _ = ∫ s, (Ioo (0 : ℝ) x).indicator (fun t ↦ q t * K t) s ∂μ₀ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK.coeFn_toLp, hq.coeFn_toLp] with s hKs hqs
      simp only [Real.inner_apply, hKs, hqs]
      by_cases hs : s ∈ Ioo (0 : ℝ) x
      · simp only [Set.indicator_of_mem hs]
        exact mul_comm _ _
      · simp only [Set.indicator_of_notMem hs, mul_zero]
    _ = ∫ s in Ioo (0 : ℝ) x, q s * K s ∂μ₀ :=
      integral_indicator measurableSet_Ioo
    _ = ∫ s in Ioo (0 : ℝ) x, q s * K s := by
      rw [Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl hx.2)]
    _ = ∫ s in (0 : ℝ)..x, q s * K s := by
      rw [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]

private theorem memLp_indicator_area_warp_test (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    MemLp ((Ioo (0 : ℝ) x).indicator (fun s ↦ x - s)) 2 μ₀ := by
  have hmeas : AEStronglyMeasurable
      ((Ioo (0 : ℝ) x).indicator (fun s ↦ x - s)) μ₀ :=
    (continuous_const.sub continuous_id).aestronglyMeasurable.indicator measurableSet_Ioo
  apply MemLp.of_bound hmeas 1
  filter_upwards with s
  by_cases hs : s ∈ Ioo (0 : ℝ) x
  · rw [Set.indicator_of_mem hs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs.2.le)]
    linarith [hs.1, hx.2]
  · simp only [Set.indicator_of_notMem hs, norm_zero]
    norm_num

/-- Weak L2 curvature pairings determine the pointwise limit of the actual
warping slope at every point of the closed normalized interval. -/
theorem tendsto_warpSlope_of_weak_L2
    (Kn : ℕ → ℝ → ℝ) (K0 : ℝ → ℝ)
    (hKn : ∀ n, MemLp (Kn n) 2 μ₀) (hK0 : MemLp K0 2 μ₀)
    (hweak : ∀ v : Lp ℝ 2 μ₀,
      Tendsto (fun n ↦ ∫ s, Kn n s * v s ∂μ₀) atTop
        (nhds (∫ s, K0 s * v s ∂μ₀)))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n ↦ warpSlope (Kn n) x) atTop (nhds (warpSlope K0 x)) := by
  have htest : MemLp ((Ioo (0 : ℝ) x).indicator (fun _ : ℝ ↦ (1 : ℝ))) 2 μ₀ :=
    MemLp.indicator measurableSet_Ioo (memLp_const (μ := μ₀) (p := 2) (1 : ℝ))
  let v : Lp ℝ 2 μ₀ := htest.toLp ((Ioo (0 : ℝ) x).indicator (fun _ : ℝ ↦ 1))
  have hid (K : ℝ → ℝ) (hK : MemLp K 2 μ₀) :
      (∫ s, K s * v s ∂μ₀) = ∫ s in (0 : ℝ)..x, K s := by
    simpa only [v, one_mul] using
      integral_mul_toLp_indicator_eq_intervalIntegral K (fun _ ↦ 1) hK x hx htest
  have hseq : (fun n ↦ ∫ s, Kn n s * v s ∂μ₀) =
      (fun n ↦ ∫ s in (0 : ℝ)..x, Kn n s) := by
    funext n
    exact hid (Kn n) (hKn n)
  have hInt := hweak v
  rw [hseq, hid K0 hK0] at hInt
  change Tendsto (fun n ↦ 2 - 2 * (∫ s in (0 : ℝ)..x, Kn n s)) atTop
    (nhds (2 - 2 * (∫ s in (0 : ℝ)..x, K0 s)))
  exact tendsto_const_nhds.sub (hInt.const_mul 2)

/-- Weak L2 curvature pairings determine the pointwise limit of the actual
warping coefficient at every point of the closed normalized interval. -/
theorem tendsto_warp_of_weak_L2
    (Kn : ℕ → ℝ → ℝ) (K0 : ℝ → ℝ)
    (hKn : ∀ n, MemLp (Kn n) 2 μ₀) (hK0 : MemLp K0 2 μ₀)
    (hweak : ∀ v : Lp ℝ 2 μ₀,
      Tendsto (fun n ↦ ∫ s, Kn n s * v s ∂μ₀) atTop
        (nhds (∫ s, K0 s * v s ∂μ₀)))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n ↦ warp (Kn n) x) atTop (nhds (warp K0 x)) := by
  have htest := memLp_indicator_area_warp_test x hx
  let v : Lp ℝ 2 μ₀ := htest.toLp ((Ioo (0 : ℝ) x).indicator (fun s ↦ x - s))
  have hid (K : ℝ → ℝ) (hK : MemLp K 2 μ₀) :
      (∫ s, K s * v s ∂μ₀) = ∫ s in (0 : ℝ)..x, (x - s) * K s := by
    exact integral_mul_toLp_indicator_eq_intervalIntegral K (fun s ↦ x - s) hK x hx htest
  have hseq : (fun n ↦ ∫ s, Kn n s * v s ∂μ₀) =
      (fun n ↦ ∫ s in (0 : ℝ)..x, (x - s) * Kn n s) := by
    funext n
    exact hid (Kn n) (hKn n)
  have hInt := hweak v
  rw [hseq, hid K0 hK0] at hInt
  change Tendsto (fun n ↦ 2 * x - 2 * (∫ s in (0 : ℝ)..x, (x - s) * Kn n s)) atTop
    (nhds (2 * x - 2 * (∫ s in (0 : ℝ)..x, (x - s) * K0 s)))
  exact tendsto_const_nhds.sub (hInt.const_mul 2)

end RicciFlowSharpEstimate.Geometry.AreaProfile
