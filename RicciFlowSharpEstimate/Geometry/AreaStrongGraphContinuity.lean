/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaRelativeWarpContinuity
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy
import RicciFlowSharpEstimate.Geometry.WeakAreaAction
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers
import Mathlib.Tactic.FieldSimp

/-!
# Continuity of the complete action in the strong area graph topology

The curvature has its actual two normalized moments. Its strong L¹ convergence
controls both actual primitives, including the relative vanishing of the warp
at the poles. Almost-everywhere curvature convergence and strong convergence
of the three parabolic graph coordinates then imply convergence of the full
action and mass. No normalization of the probe or action sublevel is assumed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem strong_graph_add
    {u v : ℕ → ℝ → ℝ} {u0 v0 : ℝ → ℝ}
    (hu : Tendsto (fun n ↦ eLpNorm (u n - u0) 2 areaμ) atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ eLpNorm (v n - v0) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm ((u n + v n) - (u0 + v0)) 2 areaμ)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n ↦ eLpNorm (u n - u0) 2 areaμ + eLpNorm (v n - v0) 2 areaμ)
      atTop (𝓝 0) := by simpa only [zero_add] using hu.add hv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) ?_
  intro n
  have heq : (u n + v n) - (u0 + v0) = (u n - u0) + (v n - v0) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  change eLpNorm ((u n + v n) - (u0 + v0)) 2 areaμ ≤
    eLpNorm (u n - u0) 2 areaμ + eLpNorm (v n - v0) 2 areaμ
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

private theorem strong_graph_sub
    {u v : ℕ → ℝ → ℝ} {u0 v0 : ℝ → ℝ}
    (hu : Tendsto (fun n ↦ eLpNorm (u n - u0) 2 areaμ) atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ eLpNorm (v n - v0) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm ((u n - v n) - (u0 - v0)) 2 areaμ)
      atTop (𝓝 0) := by
  have hneg : Tendsto (fun n ↦ eLpNorm ((-v n) - (-v0)) 2 areaμ)
      atTop (𝓝 0) := by
    simpa only [neg_sub_neg, eLpNorm_sub_comm] using hv
  simpa only [sub_eq_add_neg] using strong_graph_add hu hneg

private theorem strong_graph_coefficient_bounds {f b k w hi : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) (hhi : 0 ≤ hi)
    (hf : 0 ≤ f ∧ f ≤ hi * w) (hb : |b| ≤ 2) (hk : 0 ≤ k ∧ k ≤ hi) :
    |f * Real.sqrt f / (w * Real.sqrt w)| ≤ hi * Real.sqrt hi ∧
    |2 * b * Real.sqrt f / Real.sqrt w| ≤ 4 * Real.sqrt hi ∧
    |Real.sqrt f * k| ≤ hi * Real.sqrt hi ∧
    |k * b * f / Real.sqrt w| ≤ 2 * hi ^ 2 ∧
    |k * b ^ 2| ≤ 4 * hi ∧ |f| ≤ hi := by
  have hs : Real.sqrt f ≤ Real.sqrt hi * Real.sqrt w := by
    calc
      Real.sqrt f ≤ Real.sqrt (hi * w) := Real.sqrt_le_sqrt hf.2
      _ = Real.sqrt hi * Real.sqrt w := Real.sqrt_mul hhi w
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hfhi : f ≤ hi := hf.2.trans (mul_le_of_le_one_right hhi hw1)
  have hsfhi : Real.sqrt f ≤ Real.sqrt hi := Real.sqrt_le_sqrt hfhi
  have hwroot : w ≤ Real.sqrt w := by
    have hs1 : Real.sqrt w ≤ 1 := by
      have h := Real.sqrt_le_sqrt hw1
      simpa only [Real.sqrt_one] using h
    nlinarith only [Real.sq_sqrt hw.le, hsw.le, hs1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg f), abs_of_nonneg hk.1]
    calc
      Real.sqrt f * k ≤ Real.sqrt hi * hi :=
        mul_le_mul hsfhi hk.2 hk.1 (Real.sqrt_nonneg hi)
      _ = hi * Real.sqrt hi := mul_comm _ _
  · rw [abs_div, abs_of_pos hsw]
    apply (div_le_iff₀ hsw).2
    calc
      |k * b * f| = k * |b| * f := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk.1, abs_of_nonneg hf.1]
      _ ≤ (hi * 2) * (hi * w) :=
        mul_le_mul (mul_le_mul hk.2 hb (abs_nonneg b) hhi) hf.2 hf.1
          (mul_nonneg hhi (by norm_num))
      _ = (2 * hi ^ 2) * w := by ring
      _ ≤ (2 * hi ^ 2) * Real.sqrt w :=
        mul_le_mul_of_nonneg_left hwroot (mul_nonneg (by norm_num) (sq_nonneg hi))
  · have hbsq : b ^ 2 ≤ 4 := by
      have h := (sq_le_sq₀ (abs_nonneg b) (show (0 : ℝ) ≤ 2 by norm_num)).mpr hb
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
    rw [abs_mul, abs_of_nonneg hk.1, abs_of_nonneg (sq_nonneg b)]
    calc
      k * b ^ 2 ≤ hi * 4 := mul_le_mul hk.2 hbsq (sq_nonneg b) hhi
      _ = 4 * hi := mul_comm _ _
  · simpa only [abs_of_nonneg hf.1] using hfhi

private theorem strong_graph_operator_cancel {f b k w r p z : ℝ} (hw : 0 < w) :
    (f * Real.sqrt f / (w * Real.sqrt w)) * (w * Real.sqrt w * z) +
      (2 * b * Real.sqrt f / Real.sqrt w) * (Real.sqrt w * p) -
        (Real.sqrt f * k) * r = Real.sqrt f * (f * z + 2 * b * p - k * r) := by
  have hsw : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  field_simp [hw.ne', hsw]

private theorem strong_graph_action_eq_squares
    (K r p z : ℝ → ℝ) (hi : ℝ) (hgraph : Analysis.HasParabolicWeakDerivatives r p z)
    (hhi : 0 ≤ hi) (hK : AEStronglyMeasurable K areaμ)
    (hf : AEStronglyMeasurable (warp K) areaμ)
    (hb : AEStronglyMeasurable (warpSlope K) areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ hi)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x)))
    (hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2) :
    weakMeridionalAction K r p z =
      (∫ x, (Real.sqrt (warp K x) * weakMeridionalOperator K r p z x) ^ 2 ∂areaμ) +
      (∫ x, (Real.sqrt (warp K x) * (K x * r x)) ^ 2 ∂areaμ) -
      (∫ x, K x * warpSlope K x * warp K x * r x * p x ∂areaμ) -
      (1 / 2 : ℝ) * ∫ x, K x * (warpSlope K x) ^ 2 * (r x) ^ 2 ∂areaμ := by
  have hm := memLp_weak_operator_and_potential_of_warp_bounds K r p z hi
    hgraph hhi hK hf hb hKbox hfbox hbbox
  have hsplit :
      (∫ x, warp K x * ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2) ∂areaμ) =
      (∫ x, (Real.sqrt (warp K x) * weakMeridionalOperator K r p z x) ^ 2 ∂areaμ) +
      (∫ x, (Real.sqrt (warp K x) * (K x * r x)) ^ 2 ∂areaμ) := by
    rw [← integral_add hm.1.integrable_sq hm.2.integrable_sq]
    apply integral_congr_ae
    filter_upwards [hfbox] with x hx
    simp only [mul_pow, Real.sq_sqrt hx.1]
    ring
  rw [weakMeridionalAction_decomposition_of_warp_bounds K r p z hi
    hgraph hhi hK hf hb hKbox hfbox hbbox, hsplit]

private theorem strong_graph_action_eq_pairings
    (K r p z q : ℝ → ℝ) (hi : ℝ) (hgraph : Analysis.HasParabolicWeakDerivatives r p z)
    (hhi : 0 ≤ hi) (hK : AEStronglyMeasurable K areaμ)
    (hf : AEStronglyMeasurable (warp K) areaμ)
    (hb : AEStronglyMeasurable (warpSlope K) areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ hi)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x)))
    (hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2)
    (hq : q =ᵐ[areaμ]
      (fun x ↦ Real.sqrt (warp K x) * weakMeridionalOperator K r p z x)) :
    weakMeridionalAction K r p z =
      (∫ x, q x * q x ∂areaμ) +
      (∫ x, ((Real.sqrt (warp K x) * K x) * r x) *
        ((Real.sqrt (warp K x) * K x) * r x) ∂areaμ) -
      (∫ x, (Real.sqrt (x * (1 - x)) * p x) *
        ((K x * warpSlope K x * warp K x / Real.sqrt (x * (1 - x))) * r x) ∂areaμ) -
      (1 / 2 : ℝ) * ∫ x, r x * ((K x * (warpSlope K x) ^ 2) * r x) ∂areaμ := by
  rw [strong_graph_action_eq_squares K r p z hi hgraph hhi hK hf hb hKbox hfbox hbbox]
  have hQ : (∫ x, (Real.sqrt (warp K x) * weakMeridionalOperator K r p z x) ^ 2 ∂areaμ) =
      ∫ x, q x * q x ∂areaμ := by
    apply integral_congr_ae
    filter_upwards [hq] with x hx
    rw [hx, pow_two]
  have hE : (∫ x, (Real.sqrt (warp K x) * (K x * r x)) ^ 2 ∂areaμ) =
      ∫ x, ((Real.sqrt (warp K x) * K x) * r x) *
        ((Real.sqrt (warp K x) * K x) * r x) ∂areaμ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  have hD : (∫ x, K x * warpSlope K x * warp K x * r x * p x ∂areaμ) =
      ∫ x, (Real.sqrt (x * (1 - x)) * p x) *
        ((K x * warpSlope K x * warp K x / Real.sqrt (x * (1 - x))) * r x) ∂areaμ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hs : Real.sqrt (x * (1 - x)) ≠ 0 :=
      (Real.sqrt_pos.2 (mul_pos hx.1 (sub_pos.mpr hx.2))).ne'
    field_simp [hs]
  have hG : (∫ x, K x * (warpSlope K x) ^ 2 * (r x) ^ 2 ∂areaμ) =
      ∫ x, r x * ((K x * (warpSlope K x) ^ 2) * r x) ∂areaμ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  rw [hQ, hE, hD, hG]

/-- Strong convergence of curvature and of the three actual parabolic graph
coordinates preserves the complete action and probe mass. The conclusion also
asserts genuine integrability of the limiting complete density and mass density.
No unit-mass or complete-action bound is imposed on the approximating probes. -/
theorem action_mass_tendsto_of_strong_area_graph
    (K r : ℕ → ℝ → ℝ) (K0 r0 p0 z0 : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo)
    (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hK0 : IntegrableOn K0 (Ioo (0 : ℝ) 1))
    (hzero0 : (∫ x in (0 : ℝ)..1, K0 x) = 2)
    (hone0 : (∫ x in (0 : ℝ)..1, x * K0 x) = 1)
    (hK0box : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ hi)
    (hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0)
    (hKstrong : Tendsto (fun n ↦ ∫ x in (0 : ℝ)..1, |K n x - K0 x|)
      atTop (𝓝 0))
    (hKpoint : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ K n x) atTop (𝓝 (K0 x)))
    (hrstrong : Tendsto (fun n ↦ eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0))
    (hpstrong : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (r n) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0))
    (hzstrong : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
      atTop (𝓝 0)) :
    IntegrableOn (fun x ↦ meridionalActionDensity (warp K0 x) (warpSlope K0 x)
      (K0 x) (r0 x) (p0 x) (z0 x)) (Ioo (0 : ℝ) 1) ∧
    IntegrableOn (fun x ↦ warp K0 x * (r0 x) ^ 2) (Ioo (0 : ℝ) 1) ∧
    Tendsto (fun n ↦ meridionalAction (K n) (r n)) atTop
      (𝓝 (weakMeridionalAction K0 r0 p0 z0)) ∧
    Tendsto (fun n ↦ probeMass (K n) (r n)) atTop (𝓝 (probeMass K0 r0)) := by
  let w : ℝ → ℝ := fun x ↦ x * (1 - x)
  let f : ℕ → ℝ → ℝ := fun n ↦ warp (K n)
  let b : ℕ → ℝ → ℝ := fun n ↦ warpSlope (K n)
  let f0 : ℝ → ℝ := warp K0
  let b0 : ℝ → ℝ := warpSlope K0
  have hKi (n : ℕ) : IntegrableOn (K n) (Ioo (0 : ℝ) 1) :=
    ((hK n).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hfpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n ↦ f n x) atTop (𝓝 (f0 x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmajor : Tendsto
        (fun n ↦ 4 * x * (1 - x) * ∫ s in (0 : ℝ)..1, |K n s - K0 s|)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hKstrong.const_mul (4 * x * (1 - x))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ ↦ norm_nonneg _) ?_
    intro n
    simpa only [Real.norm_eq_abs] using abs_warp_sub_le_relative_integral_abs
      (K n) K0 (hKi n) hK0 ((hzero n).trans hzero0.symm)
      ((hone n).trans hone0.symm) x hx
  have hbpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n ↦ b n x) atTop (𝓝 (b0 x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmajor : Tendsto
        (fun n ↦ 2 * ∫ s in (0 : ℝ)..1, |K n s - K0 s|) atTop (𝓝 0) := by
      simpa only [mul_zero] using hKstrong.const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ ↦ norm_nonneg _) ?_
    intro n
    simpa only [Real.norm_eq_abs] using
      abs_warpSlope_sub_le_integral_abs_of_integrableOn (K n) K0 (hKi n) hK0 x hx
  have hhi : 0 ≤ hi :=
    hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans (hbox 0 0 (by norm_num)).2)
  have hwpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < w x :=
    mul_pos hx.1 (sub_pos.mpr hx.2)
  have hwle (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : w x ≤ 1 := by
    dsimp only [w]
    nlinarith only [hx.2, sq_nonneg x]
  have hwc : Continuous w := by dsimp only [w]; fun_prop
  have hfBounds (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ f n x ∧ f n x ≤ hi * w x := by
    have hq := warp_bounds_of_curvature_bounds (K n) (hK n) lo hi (hbox n)
      (hzero n) (hone n) x (Ioo_subset_Icc_self hx)
    refine ⟨(mul_nonneg hlo.le (hwpos x hx).le).trans ?_, ?_⟩
    · simpa only [f, w, mul_assoc] using hq.1
    · simpa only [f, w, mul_assoc] using hq.2
  have hbBounds (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |b n x| ≤ 2 :=
    abs_warpSlope_le_two (K n) (hK n)
      (fun y hy ↦ hlo.le.trans (hbox n y hy).1) (hzero n) x (Ioo_subset_Icc_self hx)
  have hf0Bounds (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ f0 x ∧ f0 x ≤ hi * w x :=
    ⟨ge_of_tendsto' (hfpoint x (Ioo_subset_Icc_self hx)) (fun n ↦ (hfBounds n x hx).1),
      le_of_tendsto' (hfpoint x (Ioo_subset_Icc_self hx)) (fun n ↦ (hfBounds n x hx).2)⟩
  have hb0Bounds (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |b0 x| ≤ 2 :=
    le_of_tendsto' (hbpoint x (Ioo_subset_Icc_self hx)).abs (fun n ↦ hbBounds n x hx)
  have hfAE : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ f n x) atTop (𝓝 (f0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hfpoint x (Ioo_subset_Icc_self hx)
  have hbAE : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ b n x) atTop (𝓝 (b0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hbpoint x (Ioo_subset_Icc_self hx)
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) areaμ := fun n ↦
    (warp_continuous (K n) (hK n)).aestronglyMeasurable
  have hbmeas : ∀ n, AEStronglyMeasurable (b n) areaμ := fun n ↦
    (warpSlope_continuous (K n) (hK n)).aestronglyMeasurable
  have hf0meas : AEStronglyMeasurable f0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hfmeas hfAE
  have hb0meas : AEStronglyMeasurable b0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hbmeas hbAE
  have hfB (n : ℕ) : ∀ᵐ x ∂areaμ, 0 ≤ f n x ∧ f n x ≤ hi * w x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hfBounds n x hx
  have hbB (n : ℕ) : ∀ᵐ x ∂areaμ, |b n x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hbBounds n x hx
  have hf0B : ∀ᵐ x ∂areaμ, 0 ≤ f0 x ∧ f0 x ≤ hi * w x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hf0Bounds x hx
  have hb0B : ∀ᵐ x ∂areaμ, |b0 x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hb0Bounds x hx
  have hKB (n : ℕ) : ∀ᵐ x ∂areaμ, 0 ≤ K n x ∧ K n x ≤ hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hlo.le.trans (hbox n x (Ioo_subset_Icc_self hx)).1,
      (hbox n x (Ioo_subset_Icc_self hx)).2⟩
  have hgraphs (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)
  have hR : ∀ n, MemLp (r n) 2 areaμ := fun n ↦ (hgraphs n).memLp
  let P : ℕ → ℝ → ℝ := fun n x ↦ Real.sqrt (w x) * deriv (r n) x
  let P0 : ℝ → ℝ := fun x ↦ Real.sqrt (w x) * p0 x
  let Z : ℕ → ℝ → ℝ := fun n x ↦ w x * Real.sqrt (w x) * deriv (deriv (r n)) x
  let Z0 : ℝ → ℝ := fun x ↦ w x * Real.sqrt (w x) * z0 x
  have hP : ∀ n, MemLp (P n) 2 areaμ := fun n ↦ (hgraphs n).memLp_weighted_deriv
  have hP0 : MemLp P0 2 areaμ := hgraph.memLp_weighted_deriv
  have hZ : ∀ n, MemLp (Z n) 2 areaμ := fun n ↦ (hgraphs n).memLp_weighted_secondDeriv
  have hZ0 : MemLp Z0 2 areaμ := hgraph.memLp_weighted_secondDeriv
  let a : ℕ → ℝ → ℝ := fun n x ↦ f n x * Real.sqrt (f n x) / (w x * Real.sqrt (w x))
  let a0 : ℝ → ℝ := fun x ↦ f0 x * Real.sqrt (f0 x) / (w x * Real.sqrt (w x))
  let c : ℕ → ℝ → ℝ := fun n x ↦ 2 * b n x * Real.sqrt (f n x) / Real.sqrt (w x)
  let c0 : ℝ → ℝ := fun x ↦ 2 * b0 x * Real.sqrt (f0 x) / Real.sqrt (w x)
  let e : ℕ → ℝ → ℝ := fun n x ↦ Real.sqrt (f n x) * K n x
  let e0 : ℝ → ℝ := fun x ↦ Real.sqrt (f0 x) * K0 x
  let d : ℕ → ℝ → ℝ := fun n x ↦ K n x * b n x * f n x / Real.sqrt (w x)
  let d0 : ℝ → ℝ := fun x ↦ K0 x * b0 x * f0 x / Real.sqrt (w x)
  let g : ℕ → ℝ → ℝ := fun n x ↦ K n x * (b n x) ^ 2
  let g0 : ℝ → ℝ := fun x ↦ K0 x * (b0 x) ^ 2
  have hsfmeas : ∀ n, AEStronglyMeasurable (fun x ↦ Real.sqrt (f n x)) areaμ :=
    fun n ↦ Real.continuous_sqrt.comp_aestronglyMeasurable (hfmeas n)
  have hsf0meas : AEStronglyMeasurable (fun x ↦ Real.sqrt (f0 x)) areaμ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf0meas
  have hameas : ∀ n, AEStronglyMeasurable (a n) areaμ := fun n ↦
    (((hfmeas n).mul (hsfmeas n)).aemeasurable.div
      (hwc.mul hwc.sqrt).aemeasurable).aestronglyMeasurable
  have ha0meas : AEStronglyMeasurable a0 areaμ :=
    ((hf0meas.mul hsf0meas).aemeasurable.div
      (hwc.mul hwc.sqrt).aemeasurable).aestronglyMeasurable
  have hcmeas : ∀ n, AEStronglyMeasurable (c n) areaμ := fun n ↦
    ((((hbmeas n).const_mul 2).mul (hsfmeas n)).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have hc0meas : AEStronglyMeasurable c0 areaμ :=
    (((hb0meas.const_mul 2).mul hsf0meas).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have hemeas : ∀ n, AEStronglyMeasurable (e n) areaμ := fun n ↦
    (hsfmeas n).mul (hK n).aestronglyMeasurable
  have he0meas : AEStronglyMeasurable e0 areaμ := hsf0meas.mul hK0.aestronglyMeasurable
  have hdmeas : ∀ n, AEStronglyMeasurable (d n) areaμ := fun n ↦
    ((((hK n).aestronglyMeasurable.mul (hbmeas n)).mul (hfmeas n)).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have hd0meas : AEStronglyMeasurable d0 areaμ :=
    (((hK0.aestronglyMeasurable.mul hb0meas).mul hf0meas).aemeasurable.div
      hwc.sqrt.aemeasurable).aestronglyMeasurable
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) areaμ := fun n ↦
    (hK n).aestronglyMeasurable.mul ((hbmeas n).pow 2)
  have hg0meas : AEStronglyMeasurable g0 areaμ :=
    hK0.aestronglyMeasurable.mul (hb0meas.pow 2)
  have hcoeff (n : ℕ) : ∀ᵐ x ∂areaμ,
      |a n x| ≤ hi * Real.sqrt hi ∧ |c n x| ≤ 4 * Real.sqrt hi ∧
      |e n x| ≤ hi * Real.sqrt hi ∧ |d n x| ≤ 2 * hi ^ 2 ∧
      |g n x| ≤ 4 * hi ∧ |f n x| ≤ hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hKB n] with x hx hkx
    exact strong_graph_coefficient_bounds (hwpos x hx) (hwle x hx) hhi
      (hfBounds n x hx) (hbBounds n x hx) hkx
  have hcoeff0 : ∀ᵐ x ∂areaμ,
      |a0 x| ≤ hi * Real.sqrt hi ∧ |c0 x| ≤ 4 * Real.sqrt hi ∧
      |e0 x| ≤ hi * Real.sqrt hi ∧ |d0 x| ≤ 2 * hi ^ 2 ∧
      |g0 x| ≤ 4 * hi ∧ |f0 x| ≤ hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hK0box] with x hx hkx
    exact strong_graph_coefficient_bounds (hwpos x hx) (hwle x hx) hhi
      (hf0Bounds x hx) (hb0Bounds x hx) hkx
  have haConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ a n x) atTop (𝓝 (a0 x)) := by
    filter_upwards [hfAE] with x hx
    exact (hx.mul hx.sqrt).div_const (w x * Real.sqrt (w x))
  have hcConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ c n x) atTop (𝓝 (c0 x)) := by
    filter_upwards [hfAE, hbAE] with x hfx hbx
    exact ((hbx.const_mul 2).mul hfx.sqrt).div_const (Real.sqrt (w x))
  have heConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ e n x) atTop (𝓝 (e0 x)) := by
    filter_upwards [hfAE, hKpoint] with x hfx hkx
    exact hfx.sqrt.mul hkx
  have hdConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ d n x) atTop (𝓝 (d0 x)) := by
    filter_upwards [hfAE, hbAE, hKpoint] with x hfx hbx hkx
    exact ((hkx.mul hbx).mul hfx).div_const (Real.sqrt (w x))
  have hgConv : ∀ᵐ x ∂areaμ, Tendsto (fun n ↦ g n x) atTop (𝓝 (g0 x)) := by
    filter_upwards [hbAE, hKpoint] with x hbx hkx
    exact hkx.mul (hbx.pow 2)
  have hAZ := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hZ hZ0 hzstrong
    hameas ha0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.1)
    (hcoeff0.mono fun _ hx ↦ hx.1) haConv
  have hCP := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hP hP0 hpstrong
    hcmeas hc0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.2.1)
    (hcoeff0.mono fun _ hx ↦ hx.2.1) hcConv
  have hER := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hR hgraph.memLp hrstrong
    hemeas he0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.2.2.1)
    (hcoeff0.mono fun _ hx ↦ hx.2.2.1) heConv
  have hDR := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hR hgraph.memLp hrstrong
    hdmeas hd0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.2.2.2.1)
    (hcoeff0.mono fun _ hx ↦ hx.2.2.2.1) hdConv
  have hGR := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hR hgraph.memLp hrstrong
    hgmeas hg0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.2.2.2.2.1)
    (hcoeff0.mono fun _ hx ↦ hx.2.2.2.2.1) hgConv
  have hFR := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hR hgraph.memLp hrstrong
    hfmeas hf0meas (fun n ↦ (hcoeff n).mono fun _ hx ↦ hx.2.2.2.2.2)
    (hcoeff0.mono fun _ hx ↦ hx.2.2.2.2.2) hfAE
  let Q : ℕ → ℝ → ℝ := fun n x ↦ a n x * Z n x + c n x * P n x - e n x * r n x
  let Q0 : ℝ → ℝ := fun x ↦ a0 x * Z0 x + c0 x * P0 x - e0 x * r0 x
  have hQ : ∀ n, MemLp (Q n) 2 areaμ := fun n ↦
    ((hAZ.1 n).add (hCP.1 n)).sub (hER.1 n)
  have hQ0 : MemLp Q0 2 areaμ := (hAZ.2.1.add hCP.2.1).sub hER.2.1
  have hQstrong : Tendsto (fun n ↦ eLpNorm (Q n - Q0) 2 areaμ) atTop (𝓝 0) :=
    strong_graph_sub (strong_graph_add hAZ.2.2 hCP.2.2) hER.2.2
  have hQpair := Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hQ hQ0 hQ hQ0 hQstrong hQstrong
  have hEpair := Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hER.1 hER.2.1 hER.1 hER.2.1 hER.2.2 hER.2.2
  have hDpair := Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hP hP0 hDR.1 hDR.2.1 hpstrong hDR.2.2
  have hGpair := Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hR hgraph.memLp hGR.1 hGR.2.1 hrstrong hGR.2.2
  have hFpair := Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hR hgraph.memLp hFR.1 hFR.2.1 hrstrong hFR.2.2
  have hQeq (n : ℕ) : Q n =ᵐ[areaμ]
      (fun x ↦ Real.sqrt (f n x) *
        weakMeridionalOperator (K n) (r n) (deriv (r n)) (deriv (deriv (r n))) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact strong_graph_operator_cancel (hwpos x hx)
  have hQeq0 : Q0 =ᵐ[areaμ]
      (fun x ↦ Real.sqrt (f0 x) * weakMeridionalOperator K0 r0 p0 z0 x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact strong_graph_operator_cancel (hwpos x hx)
  have hDensity : IntegrableOn (fun x ↦
      meridionalActionDensity (warp K0 x) (warpSlope K0 x) (K0 x) (r0 x) (p0 x) (z0 x))
      (Ioo (0 : ℝ) 1) :=
    integrable_weakMeridionalActionDensity_of_warp_bounds K0 r0 p0 z0 hi hgraph
      hhi hK0.aestronglyMeasurable hf0meas hb0meas hK0box hf0B hb0B
  have hMass : IntegrableOn (fun x ↦ warp K0 x * (r0 x) ^ 2) (Ioo (0 : ℝ) 1) := by
    apply hFpair.2.1.congr
    exact Eventually.of_forall fun x ↦ by dsimp only [f0]; ring
  have hActionEq (n : ℕ) : meridionalAction (K n) (r n) =
      (∫ x, Q n x * Q n x ∂areaμ) +
      (∫ x, (e n x * r n x) * (e n x * r n x) ∂areaμ) -
      (∫ x, P n x * (d n x * r n x) ∂areaμ) -
      (1 / 2 : ℝ) * ∫ x, r n x * (g n x * r n x) ∂areaμ := by
    simpa only [weakMeridionalAction_deriv, e, f, P, w, d, b, g] using
      strong_graph_action_eq_pairings (K n) (r n) (deriv (r n))
        (deriv (deriv (r n))) (Q n) hi (hgraphs n) hhi
        (hK n).aestronglyMeasurable (hfmeas n) (hbmeas n)
        (hKB n) (hfB n) (hbB n) (hQeq n)
  have hActionEq0 : weakMeridionalAction K0 r0 p0 z0 =
      (∫ x, Q0 x * Q0 x ∂areaμ) +
      (∫ x, (e0 x * r0 x) * (e0 x * r0 x) ∂areaμ) -
      (∫ x, P0 x * (d0 x * r0 x) ∂areaμ) -
      (1 / 2 : ℝ) * ∫ x, r0 x * (g0 x * r0 x) ∂areaμ := by
    simpa only [e0, f0, P0, w, d0, b0, g0] using
      strong_graph_action_eq_pairings K0 r0 p0 z0 Q0 hi hgraph hhi
        hK0.aestronglyMeasurable hf0meas hb0meas hK0box hf0B hb0B hQeq0
  have hMassEq (K' r' : ℝ → ℝ) : probeMass K' r' =
      ∫ x, r' x * (warp K' x * r' x) ∂areaμ := by
    rw [probeMass, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  refine ⟨hDensity, hMass, ?_, ?_⟩
  · simpa only [hActionEq, hActionEq0] using
      ((hQpair.2.2.add hEpair.2.2).sub hDpair.2.2).sub (hGpair.2.2.const_mul (1 / 2 : ℝ))
  · simpa only [hMassEq, f, f0] using hFpair.2.2

end RicciFlowSharpEstimate.Geometry.AreaProfile
