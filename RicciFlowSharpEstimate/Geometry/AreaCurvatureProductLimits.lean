/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaSublevelGraphBounds
import RicciFlowSharpEstimate.Analysis.L2PointwiseProducts
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers
import RicciFlowSharpEstimate.Analysis.BoundedWeakPairingLimits

/-!
# Limits of the curvature-linear complete-action terms

The normalized complete action supplies a uniform parabolic graph bound.
Strong L² convergence of the actual probes then gives strong L¹ convergence
of each varying test against the bounded weak curvature sequence. This treats
the curvature square factor weakly in L² and both literal curvature-linear
remainder integrals, throughout the full physical interval.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem integral_sq_le_of_ae_abs_le
    {u v : ℝ → ℝ} {C : ℝ} (hu : MemLp u 2 areaμ) (hv : MemLp v 2 areaμ)
    (h : ∀ᵐ x ∂areaμ, |u x| ≤ C * |v x|) :
    (∫ x, u x ^ 2 ∂areaμ) ≤ C ^ 2 * (∫ x, v x ^ 2 ∂areaμ) := by
  rw [← integral_const_mul]
  apply integral_mono_ae hu.integrable_sq (hv.integrable_sq.const_mul (C ^ 2))
  filter_upwards [h] with x hx
  have hs := mul_self_le_mul_self (abs_nonneg (u x)) hx
  simpa only [← pow_two, mul_pow, sq_abs] using hs

private theorem abs_slope_warp_mul_le
    {f b p w hi : ℝ} (hhi : 0 ≤ hi) (hw : w ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ hi * w) (hb : |b| ≤ 2) :
    |b * f * p| ≤ (2 * hi) * |Real.sqrt w * p| := by
  have hfs : f ≤ hi * Real.sqrt w :=
    hf.2.trans (mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr hw) hhi)
  calc
    |b * f * p| = (|b| * f) * |p| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hf.1]
    _ ≤ (2 * (hi * Real.sqrt w)) * |p| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hb hfs hf.1 (by norm_num)) (abs_nonneg p)
    _ = (2 * hi) * |Real.sqrt w * p| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg w)]
      ring

private theorem abs_slope_sq_mul_le {b r : ℝ} (hb : |b| ≤ 2) :
    |b ^ 2 * r| ≤ 4 * |r| := by
  have hbsq : b ^ 2 ≤ 4 := by
    have hs := (sq_le_sq₀ (abs_nonneg b) (show (0 : ℝ) ≤ 2 by norm_num)).mpr hb
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
  rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
  exact mul_le_mul_of_nonneg_right hbsq (abs_nonneg r)

private theorem curvature_pairing_of_strong_probe
    {K : ℕ → ℝ → ℝ} {K0 : ℝ → ℝ} {r : ℕ → ℝ → ℝ} {r0 : ℝ → ℝ}
    {u : ℕ → ℝ → ℝ} {u0 : ℝ → ℝ} {hi M : ℝ}
    (hK : ∀ n, AEStronglyMeasurable (K n) areaμ)
    (hK0 : AEStronglyMeasurable K0 areaμ)
    (hKB : ∀ n, ∀ᵐ x ∂areaμ, |K n x| ≤ hi)
    (hK0B : ∀ᵐ x ∂areaμ, |K0 x| ≤ hi)
    (hweak : ∀ v : ℝ → ℝ, Integrable v areaμ →
      Tendsto (fun n => ∫ x, K n x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K0 x * v x ∂areaμ)))
    (hr : ∀ n, MemLp (r n) 2 areaμ) (hr0 : MemLp r0 2 areaμ)
    (hu : ∀ n, MemLp (u n) 2 areaμ) (hu0 : MemLp u0 2 areaμ)
    (hM : ∀ n, (∫ x, u n x ^ 2 ∂areaμ) ≤ M)
    (hstrong : Tendsto (fun n => eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0))
    (hpoint : ∀ᵐ x ∂areaμ, Tendsto (fun n => u n x) atTop (𝓝 (u0 x))) :
    Integrable (fun x => K0 x * (r0 x * u0 x)) areaμ ∧
      Tendsto (fun n => ∫ x, K n x * (r n x * u n x) ∂areaμ) atTop
        (𝓝 (∫ x, K0 x * (r0 x * u0 x) ∂areaμ)) := by
  exact Analysis.integrable_and_tendsto_mul_of_bounded_weak_pairing
    hK hK0 hKB hK0B hweak (fun n => (hr n).integrable_mul (hu n))
    (hr0.integrable_mul hu0)
    (Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      hr hr0 hu M hM hstrong hpoint)

/-- On a normalized complete-action sublevel, actual weak curvature
pairings and strong probe convergence pass all curvature-linear terms to
the tied weak derivative graph. The curvature square factor converges
weakly in genuine L²; both literal remainder integrals converge and their
limits are integrable. No derivative of curvature or endpoint trace is
assumed. -/
theorem curvature_action_pairings_tendsto
    (K r : ℕ → ℝ → ℝ) (K0 r0 p0 z0 : ℝ → ℝ) (lo hi B : ℝ)
    (hlo : 0 < lo)
    (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B)
    (hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0)
    (hstrong : Tendsto (fun n => eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0))
    (hrpoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n => r n x) atTop (𝓝 (r0 x)))
    (hppoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n => deriv (r n) x) atTop (𝓝 (p0 x)))
    (hfpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => warp (K n) x) atTop (𝓝 (warp K0 x)))
    (hbpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => warpSlope (K n) x) atTop (𝓝 (warpSlope K0 x)))
    (hf0 : ContinuousOn (warp K0) (Icc (0 : ℝ) 1))
    (hb0 : ContinuousOn (warpSlope K0) (Icc (0 : ℝ) 1))
    (hK0 : AEStronglyMeasurable K0 areaμ)
    (hK0box : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ hi)
    (hweak : ∀ v : ℝ → ℝ, Integrable v areaμ →
      Tendsto (fun n => ∫ x, K n x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K0 x * v x ∂areaμ))) :
    ((∀ n, MemLp (fun x => Real.sqrt (warp (K n) x) * (K n x * r n x)) 2 areaμ) ∧
      MemLp (fun x => Real.sqrt (warp K0 x) * (K0 x * r0 x)) 2 areaμ ∧
      ∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x,
          (Real.sqrt (warp (K n) x) * (K n x * r n x)) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (Real.sqrt (warp K0 x) * (K0 x * r0 x)) * v x ∂areaμ))) ∧
    (Integrable (fun x => K0 x * warpSlope K0 x * warp K0 x * r0 x * p0 x) areaμ ∧
      Tendsto (fun n => ∫ x,
        K n x * warpSlope (K n) x * warp (K n) x * r n x * deriv (r n) x ∂areaμ)
        atTop (𝓝 (∫ x, K0 x * warpSlope K0 x * warp K0 x * r0 x * p0 x ∂areaμ))) ∧
    (Integrable (fun x => K0 x * (warpSlope K0 x) ^ 2 * r0 x ^ 2) areaμ ∧
      Tendsto (fun n => ∫ x, K n x * (warpSlope (K n) x) ^ 2 * r n x ^ 2 ∂areaμ)
        atTop (𝓝 (∫ x, K0 x * (warpSlope K0 x) ^ 2 * r0 x ^ 2 ∂areaμ))) := by
  let f : ℕ → ℝ → ℝ := fun n => warp (K n)
  let b : ℕ → ℝ → ℝ := fun n => warpSlope (K n)
  let f0 : ℝ → ℝ := warp K0
  let b0 : ℝ → ℝ := warpSlope K0
  let w : ℝ → ℝ := fun x => x * (1 - x)
  have hhi : 0 ≤ hi :=
    hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans (hbox 0 0 (by norm_num)).2)
  have hgraphN (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)
  have hrmem (n : ℕ) : MemLp (r n) 2 areaμ := (hgraphN n).memLp
  have hKmeas (n : ℕ) : AEStronglyMeasurable (K n) areaμ :=
    (hK n).aestronglyMeasurable
  have hfmeas (n : ℕ) : AEStronglyMeasurable (f n) areaμ :=
    (warp_continuous (K n) (hK n)).aestronglyMeasurable
  have hbmeas (n : ℕ) : AEStronglyMeasurable (b n) areaμ :=
    (warpSlope_continuous (K n) (hK n)).aestronglyMeasurable
  have hf0meas : AEStronglyMeasurable f0 areaμ :=
    ((hf0.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hb0meas : AEStronglyMeasurable b0 areaμ :=
    ((hb0.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hw : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ w x ∧ w x ≤ 1 := by
    intro x hx
    refine ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), ?_⟩
    dsimp only [w]
    nlinarith only [hx.2, sq_nonneg x]
  have hfB (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ f n x ∧ f n x ≤ hi * w x := by
    have h := warp_bounds_of_curvature_bounds (K n) (hK n) lo hi
      (hbox n) (hzero n) (hone n) x hx
    refine ⟨(mul_nonneg (mul_nonneg hlo.le hx.1) (sub_nonneg.mpr hx.2)).trans h.1, ?_⟩
    simpa only [w, mul_assoc] using h.2
  have hbB (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |b n x| ≤ 2 :=
    abs_warpSlope_le_two (K n) (hK n)
      (fun y hy => hlo.le.trans (hbox n y hy).1) (hzero n) x hx
  have hf0B (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ f0 x ∧ f0 x ≤ hi * w x :=
    ⟨ge_of_tendsto' (hfpoint x hx) (fun n => (hfB n x hx).1),
      le_of_tendsto' (hfpoint x hx) (fun n => (hfB n x hx).2)⟩
  have hb0B (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |b0 x| ≤ 2 :=
    le_of_tendsto' (hbpoint x hx).abs (fun n => hbB n x hx)
  have hKB (n : ℕ) : ∀ᵐ x ∂areaμ, |K n x| ≤ hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := hbox n x ⟨hx.1.le, hx.2.le⟩
    simpa only [abs_of_nonneg (hlo.le.trans h.1)] using h.2
  have hK0B : ∀ᵐ x ∂areaμ, |K0 x| ≤ hi := by
    filter_upwards [hK0box] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  obtain ⟨M, _, hM⟩ := exists_uniform_parabolic_graph_bound lo hi hlo hhi B
  have hbounds (n : ℕ) := hM (K n) (r n) (hK n) (hr n) (hbox n)
    (hzero n) (hone n) (hmass n) (hA n)
  have hsB (n : ℕ) : ∀ᵐ x ∂areaμ, |Real.sqrt (f n x)| ≤ Real.sqrt hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((hfB n x ⟨hx.1.le, hx.2.le⟩).2.trans
      (mul_le_of_le_one_right hhi (hw x hx).2))
  have hs0B : ∀ᵐ x ∂areaμ, |Real.sqrt (f0 x)| ≤ Real.sqrt hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((hf0B x ⟨hx.1.le, hx.2.le⟩).2.trans
      (mul_le_of_le_one_right hhi (hw x hx).2))
  have hsmeas (n : ℕ) : AEStronglyMeasurable (fun x => Real.sqrt (f n x)) areaμ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hfmeas n)
  have hs0meas : AEStronglyMeasurable (fun x => Real.sqrt (f0 x)) areaμ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf0meas
  have hpot (n : ℕ) :
      MemLp (fun x => Real.sqrt (f n x) * (K n x * r n x)) 2 areaμ := by
    have hcoeff : ∀ᵐ x ∂areaμ,
        |Real.sqrt (f n x) * K n x| ≤ Real.sqrt hi * hi := by
      filter_upwards [hsB n, hKB n] with x hs hk
      rw [abs_mul]
      exact mul_le_mul hs hk (abs_nonneg _) (Real.sqrt_nonneg hi)
    simpa only [Pi.mul_apply, mul_assoc] using
      Analysis.memLp_mul_of_ae_abs_le ((hsmeas n).mul (hKmeas n)) hcoeff (hrmem n)
  have hpot0 : MemLp (fun x => Real.sqrt (f0 x) * (K0 x * r0 x)) 2 areaμ := by
    have hcoeff : ∀ᵐ x ∂areaμ, |Real.sqrt (f0 x) * K0 x| ≤ Real.sqrt hi * hi := by
      filter_upwards [hs0B, hK0B] with x hs hk
      rw [abs_mul]
      exact mul_le_mul hs hk (abs_nonneg _) (Real.sqrt_nonneg hi)
    simpa only [Pi.mul_apply, mul_assoc] using
      Analysis.memLp_mul_of_ae_abs_le (hs0meas.mul hK0) hcoeff hgraph.memLp
  have hpotWeak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, (Real.sqrt (f n x) * (K n x * r n x)) * v x ∂areaμ)
        atTop (𝓝 (∫ x, (Real.sqrt (f0 x) * (K0 x * r0 x)) * v x ∂areaμ)) := by
    intro v
    have hu (n : ℕ) : MemLp (fun x => Real.sqrt (f n x) * v x) 2 areaμ :=
      Analysis.memLp_mul_of_ae_abs_le (hsmeas n) (hsB n) (Lp.memLp v)
    have hu0 : MemLp (fun x => Real.sqrt (f0 x) * v x) 2 areaμ :=
      Analysis.memLp_mul_of_ae_abs_le hs0meas hs0B (Lp.memLp v)
    have huBound (n : ℕ) : (∫ x, (Real.sqrt (f n x) * v x) ^ 2 ∂areaμ) ≤
        (Real.sqrt hi) ^ 2 * (∫ x, (v x) ^ 2 ∂areaμ) := by
      apply integral_sq_le_of_ae_abs_le (hu n) (Lp.memLp v)
      filter_upwards [hsB n] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have huPoint : ∀ᵐ x ∂areaμ,
        Tendsto (fun n => Real.sqrt (f n x) * v x) atTop
          (𝓝 (Real.sqrt (f0 x) * v x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hfpoint x ⟨hx.1.le, hx.2.le⟩).sqrt.mul_const (v x)
    have h := curvature_pairing_of_strong_probe hKmeas hK0 hKB hK0B hweak
      hrmem hgraph.memLp hu hu0 huBound hstrong huPoint
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h.2
  let u : ℕ → ℝ → ℝ := fun n x => b n x * f n x * deriv (r n) x
  let u0 : ℝ → ℝ := fun x => b0 x * f0 x * p0 x
  have huCompare (n : ℕ) : ∀ᵐ x ∂areaμ,
      |u n x| ≤ (2 * hi) * |Real.sqrt (w x) * deriv (r n) x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact abs_slope_warp_mul_le hhi (hw x hx).2
      (hfB n x ⟨hx.1.le, hx.2.le⟩) (hbB n x ⟨hx.1.le, hx.2.le⟩)
  have hu (n : ℕ) : MemLp (u n) 2 areaμ := by
    apply (hgraphN n).memLp_weighted_deriv.of_le_mul (c := 2 * hi)
      (((hbmeas n).mul (hfmeas n)).mul
        ((hr n).continuous_deriv (by norm_num)).aestronglyMeasurable)
    simpa only [Real.norm_eq_abs, Pi.mul_apply, u, w] using huCompare n
  have hu0 : MemLp u0 2 areaμ := by
    apply hgraph.memLp_weighted_deriv.of_le_mul (c := 2 * hi)
      ((hb0meas.mul hf0meas).mul hgraph.weakDeriv.locallyIntegrable_deriv.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs, Pi.mul_apply, w] using
      abs_slope_warp_mul_le (p := p0 x) hhi (hw x hx).2
        (hf0B x ⟨hx.1.le, hx.2.le⟩) (hb0B x ⟨hx.1.le, hx.2.le⟩)
  have huBound (n : ℕ) : (∫ x, u n x ^ 2 ∂areaμ) ≤ (2 * hi) ^ 2 * M :=
    (integral_sq_le_of_ae_abs_le (hu n) (hgraphN n).memLp_weighted_deriv
      (huCompare n)).trans
        (mul_le_mul_of_nonneg_left (hbounds n).2.1 (sq_nonneg (2 * hi)))
  have huPoint : ∀ᵐ x ∂areaμ, Tendsto (fun n => u n x) atTop (𝓝 (u0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hbpoint x ⟨hx.1.le, hx.2.le⟩).mul
      (hfpoint x ⟨hx.1.le, hx.2.le⟩)).mul (hppoint x hx)
  have hMixed := curvature_pairing_of_strong_probe hKmeas hK0 hKB hK0B hweak
    hrmem hgraph.memLp hu hu0 huBound hstrong huPoint
  let q : ℕ → ℝ → ℝ := fun n x => (b n x) ^ 2 * r n x
  let q0 : ℝ → ℝ := fun x => (b0 x) ^ 2 * r0 x
  have hqCompare (n : ℕ) : ∀ᵐ x ∂areaμ, |q n x| ≤ 4 * |r n x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact abs_slope_sq_mul_le (hbB n x ⟨hx.1.le, hx.2.le⟩)
  have hq (n : ℕ) : MemLp (q n) 2 areaμ := by
    apply (hrmem n).of_le_mul (c := 4)
      (((hbmeas n).pow 2).mul (hrmem n).aestronglyMeasurable)
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.pow_apply, q] using hqCompare n
  have hq0 : MemLp q0 2 areaμ := by
    apply hgraph.memLp.of_le_mul (c := 4)
      ((hb0meas.pow 2).mul hgraph.memLp.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.pow_apply] using
      abs_slope_sq_mul_le (r := r0 x) (hb0B x ⟨hx.1.le, hx.2.le⟩)
  have hqBound (n : ℕ) : (∫ x, q n x ^ 2 ∂areaμ) ≤ (4 : ℝ) ^ 2 * M :=
    (integral_sq_le_of_ae_abs_le (hq n) (hrmem n) (hqCompare n)).trans
      (mul_le_mul_of_nonneg_left (hbounds n).1 (sq_nonneg (4 : ℝ)))
  have hqPoint : ∀ᵐ x ∂areaμ, Tendsto (fun n => q n x) atTop (𝓝 (q0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hbpoint x ⟨hx.1.le, hx.2.le⟩).pow 2).mul (hrpoint x hx)
  have hNegative := curvature_pairing_of_strong_probe hKmeas hK0 hKB hK0B hweak
    hrmem hgraph.memLp hq hq0 hqBound hstrong hqPoint
  refine ⟨⟨hpot, hpot0, hpotWeak⟩, ?_, ?_⟩
  · simpa only [u, u0, f, f0, b, b0, mul_assoc, mul_left_comm, mul_comm] using hMixed
  · simpa only [q, q0, b, b0, pow_two, mul_assoc, mul_left_comm, mul_comm] using hNegative

end RicciFlowSharpEstimate.Geometry.AreaProfile
