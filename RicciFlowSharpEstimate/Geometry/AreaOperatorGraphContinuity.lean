/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature
import RicciFlowSharpEstimate.Geometry.AreaRelativeWarpContinuity
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers
import RicciFlowSharpEstimate.Analysis.L2PointwiseProducts

/-!
# Strong continuity of the actual operator in the parabolic graph

Curvature convergence and the three genuine graph limits imply convergence
of the meridional source with the fixed square-root parabolic weight. The
returned source is the actual operator of the same limiting weak jets.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped ENNReal Topology ContDiff

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem weighted_operator_graph_add
    {u v : ℕ → ℝ → ℝ} {u0 v0 : ℝ → ℝ}
    (hu : Tendsto (fun n => eLpNorm (u n - u0) 2 areaμ) atTop (𝓝 0))
    (hv : Tendsto (fun n => eLpNorm (v n - v0) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((u n + v n) - (u0 + v0)) 2 areaμ)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => eLpNorm (u n - u0) 2 areaμ + eLpNorm (v n - v0) 2 areaμ)
      atTop (𝓝 0) := by simpa only [zero_add] using hu.add hv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro n
  have heq : (u n + v n) - (u0 + v0) = (u n - u0) + (v n - v0) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  change eLpNorm ((u n + v n) - (u0 + v0)) 2 areaμ ≤
    eLpNorm (u n - u0) 2 areaμ + eLpNorm (v n - v0) 2 areaμ
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

private theorem weighted_operator_graph_sub
    {u v : ℕ → ℝ → ℝ} {u0 v0 : ℝ → ℝ}
    (hu : Tendsto (fun n => eLpNorm (u n - u0) 2 areaμ) atTop (𝓝 0))
    (hv : Tendsto (fun n => eLpNorm (v n - v0) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((u n - v n) - (u0 - v0)) 2 areaμ)
      atTop (𝓝 0) := by
  have hneg : Tendsto (fun n => eLpNorm ((-v n) - (-v0)) 2 areaμ)
      atTop (𝓝 0) := by
    simpa only [neg_sub_neg, eLpNorm_sub_comm] using hv
  simpa only [sub_eq_add_neg] using weighted_operator_graph_add hu hneg

private theorem weighted_operator_coefficient_bounds {f b k w hi : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ hi * w) (hb : |b| ≤ 2) (hk : 0 ≤ k ∧ k ≤ hi) :
    |f / w| ≤ hi ∧ |2 * b| ≤ 4 ∧ |Real.sqrt w * k| ≤ hi := by
  have hs : Real.sqrt w ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw1
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hf.1 hw.le)]
    exact (div_le_iff₀ hw).mpr hf.2
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hb]
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg w), abs_of_nonneg hk.1]
    calc
      Real.sqrt w * k ≤ 1 * k := mul_le_mul_of_nonneg_right hs hk.1
      _ = k := one_mul k
      _ ≤ hi := hk.2

private theorem weighted_operator_cancel {f b k w r p z : ℝ} (hw : 0 < w) :
    (f / w) * (w * Real.sqrt w * z) + (2 * b) * (Real.sqrt w * p) -
      (Real.sqrt w * k) * r = Real.sqrt w * (f * z + 2 * b * p - k * r) := by
  field_simp [hw.ne']

/-- Curvature L² convergence and the three strong parabolic graph limits give
the actual weighted operator limit in L², for the same curvature and weak jets.
The probes are not mass-normalized, and no operator limit is assumed. -/
theorem weighted_meridionalOperator_tendsto_of_strong_graph
    (C : ℝ) (hC : 1 ≤ C) (K r : ℕ → ℝ → ℝ) (K0 r0 p0 z0 : ℝ → ℝ)
    (hK : ∀ n, IsSmoothAreaCurvature C (K n))
    (hK0 : IsBoundedAreaCurvature C K0)
    (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0)
    (hKstrong : Tendsto (fun n => eLpNorm (K n - K0) 2 areaμ) atTop (𝓝 0))
    (hKpoint : ∀ᵐ x ∂areaμ, Tendsto (fun n => K n x) atTop (𝓝 (K0 x)))
    (hrstrong : Tendsto (fun n => eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0))
    (hpstrong : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (r n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0))
    (hzstrong : Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
      atTop (𝓝 0)) :
    (∀ n, MemLp (fun x => Real.sqrt (x * (1 - x)) * meridionalOperator (K n) (r n) x)
      2 areaμ) ∧
    MemLp (fun x => Real.sqrt (x * (1 - x)) * weakMeridionalOperator K0 r0 p0 z0 x)
      2 areaμ ∧
    Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * meridionalOperator (K n) (r n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * weakMeridionalOperator K0 r0 p0 z0 x))
      2 areaμ) atTop (𝓝 0) := by
  let w : ℝ → ℝ := fun x => x * (1 - x)
  let f : ℕ → ℝ → ℝ := fun n => warp (K n)
  let b : ℕ → ℝ → ℝ := fun n => warpSlope (K n)
  let f0 : ℝ → ℝ := warp K0
  let b0 : ℝ → ℝ := warpSlope K0
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlo : 0 ≤ 2 / C := by positivity
  have hKm (n : ℕ) := (hK n).memLp_curvature
  have hK0m := hK0.memLp_curvature
  have hKi (n : ℕ) : IntegrableOn (K n) (Ioo (0 : ℝ) 1) :=
    (hKm n).integrable (by norm_num)
  have hK0i : IntegrableOn K0 (Ioo (0 : ℝ) 1) := hK0m.integrable (by norm_num)
  have hL1 : Tendsto (fun n => ∫ x, |K n x - K0 x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := K) (g := K0) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      hKm hK0m (fun _ => hc) (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl)
      hKstrong (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |K n x - K0 x|) atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hfpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => f n x) atTop (𝓝 (f0 x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmajor : Tendsto
        (fun n => 4 * x * (1 - x) * ∫ s in (0 : ℝ)..1, |K n s - K0 s|)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hL1I.const_mul (4 * x * (1 - x))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ => norm_nonneg _) ?_
    intro n
    simpa only [Real.norm_eq_abs] using abs_warp_sub_le_relative_integral_abs
      (K n) K0 (hKi n) hK0i ((hK n).2.2.1.trans hK0.2.2.1.symm)
      ((hK n).2.2.2.trans hK0.2.2.2.symm) x hx
  have hbpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => b n x) atTop (𝓝 (b0 x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmajor : Tendsto
        (fun n => 2 * ∫ s in (0 : ℝ)..1, |K n s - K0 s|) atTop (𝓝 0) := by
      simpa only [mul_zero] using hL1I.const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ => norm_nonneg _) ?_
    intro n
    simpa only [Real.norm_eq_abs] using
      abs_warpSlope_sub_le_integral_abs_of_integrableOn (K n) K0 (hKi n) hK0i x hx
  have hwpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < w x :=
    mul_pos hx.1 (sub_pos.mpr hx.2)
  have hwle (x : ℝ) : w x ≤ 1 := by
    dsimp [w]
    nlinarith only [sq_nonneg (x - 1 / 2)]
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hfBounds (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ f n x ∧ f n x ≤ (2 * C) * w x := by
    have hb := (hK n).geometry_bounds x (Ioo_subset_Icc_self hx)
    refine ⟨?_, ?_⟩
    · exact (mul_nonneg (mul_nonneg hlo hx.1.le) (sub_nonneg.mpr hx.2.le)).trans hb.1
    · simpa only [f, w, mul_assoc] using hb.2.1
  have hbBounds (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |b n x| ≤ 2 :=
    ((hK n).geometry_bounds x (Ioo_subset_Icc_self hx)).2.2
  have hKBounds (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ K n x ∧ K n x ≤ 2 * C := by
    have hb := (hK n).common_bounds x (Ioo_subset_Icc_self hx)
    exact ⟨hlo.trans hb.1, hb.2⟩
  have hf0Bounds (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ f0 x ∧ f0 x ≤ (2 * C) * w x :=
    ⟨ge_of_tendsto' (hfpoint x (Ioo_subset_Icc_self hx)) (fun n => (hfBounds n x hx).1),
      le_of_tendsto' (hfpoint x (Ioo_subset_Icc_self hx)) (fun n => (hfBounds n x hx).2)⟩
  have hb0Bounds (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |b0 x| ≤ 2 :=
    le_of_tendsto' (hbpoint x (Ioo_subset_Icc_self hx)).abs (fun n => hbBounds n x hx)
  have hK0Bounds : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ 2 * C := by
    filter_upwards [hKpoint, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact ⟨ge_of_tendsto' hx (fun n => (hKBounds n x hxI).1),
      le_of_tendsto' hx (fun n => (hKBounds n x hxI).2)⟩
  have hfAE : ∀ᵐ x ∂areaμ, Tendsto (fun n => f n x) atTop (𝓝 (f0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hfpoint x (Ioo_subset_Icc_self hx)
  have hbAE : ∀ᵐ x ∂areaμ, Tendsto (fun n => b n x) atTop (𝓝 (b0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hbpoint x (Ioo_subset_Icc_self hx)
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) areaμ := fun n =>
    (warp_continuous (K n) (hK n).1.continuous).aestronglyMeasurable
  have hbmeas : ∀ n, AEStronglyMeasurable (b n) areaμ := fun n =>
    (warpSlope_continuous (K n) (hK n).1.continuous).aestronglyMeasurable
  have hf0meas : AEStronglyMeasurable f0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hfmeas hfAE
  have hb0meas : AEStronglyMeasurable b0 areaμ :=
    aestronglyMeasurable_of_tendsto_ae atTop hbmeas hbAE
  let P : ℕ → ℝ → ℝ := fun n x => Real.sqrt (w x) * deriv (r n) x
  let P0 : ℝ → ℝ := fun x => Real.sqrt (w x) * p0 x
  let Z : ℕ → ℝ → ℝ := fun n x => w x * Real.sqrt (w x) * deriv (deriv (r n)) x
  let Z0 : ℝ → ℝ := fun x => w x * Real.sqrt (w x) * z0 x
  let a : ℕ → ℝ → ℝ := fun n x => f n x / w x
  let a0 : ℝ → ℝ := fun x => f0 x / w x
  let c : ℕ → ℝ → ℝ := fun n x => 2 * b n x
  let c0 : ℝ → ℝ := fun x => 2 * b0 x
  let e : ℕ → ℝ → ℝ := fun n x => Real.sqrt (w x) * K n x
  let e0 : ℝ → ℝ := fun x => Real.sqrt (w x) * K0 x
  have hameas : ∀ n, AEStronglyMeasurable (a n) areaμ := fun n =>
    ((hfmeas n).aemeasurable.div hwc.aemeasurable).aestronglyMeasurable
  have ha0meas : AEStronglyMeasurable a0 areaμ :=
    (hf0meas.aemeasurable.div hwc.aemeasurable).aestronglyMeasurable
  have hcmeas : ∀ n, AEStronglyMeasurable (c n) areaμ := fun n => (hbmeas n).const_mul 2
  have hc0meas : AEStronglyMeasurable c0 areaμ := hb0meas.const_mul 2
  have hemeas : ∀ n, AEStronglyMeasurable (e n) areaμ := fun n =>
    hwc.sqrt.aestronglyMeasurable.mul (hK n).1.continuous.aestronglyMeasurable
  have he0meas : AEStronglyMeasurable e0 areaμ := hwc.sqrt.aestronglyMeasurable.mul hK0.1
  have hcoeff (n : ℕ) : ∀ᵐ x ∂areaμ,
      |a n x| ≤ 2 * C ∧ |c n x| ≤ 4 ∧ |e n x| ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact weighted_operator_coefficient_bounds (hwpos x hx) (hwle x)
      (hfBounds n x hx) (hbBounds n x hx) (hKBounds n x hx)
  have hcoeff0 : ∀ᵐ x ∂areaμ, |a0 x| ≤ 2 * C ∧ |c0 x| ≤ 4 ∧ |e0 x| ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hK0Bounds] with x hx hkx
    exact weighted_operator_coefficient_bounds (hwpos x hx) (hwle x)
      (hf0Bounds x hx) (hb0Bounds x hx) hkx
  have haConv : ∀ᵐ x ∂areaμ, Tendsto (fun n => a n x) atTop (𝓝 (a0 x)) := by
    filter_upwards [hfAE] with x hx
    exact hx.div_const (w x)
  have hcConv : ∀ᵐ x ∂areaμ, Tendsto (fun n => c n x) atTop (𝓝 (c0 x)) := by
    filter_upwards [hbAE] with x hx
    exact hx.const_mul 2
  have heConv : ∀ᵐ x ∂areaμ, Tendsto (fun n => e n x) atTop (𝓝 (e0 x)) := by
    filter_upwards [hKpoint] with x hx
    exact hx.const_mul (Real.sqrt (w x))
  have hgraphs (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)
  have hR : ∀ n, MemLp (r n) 2 areaμ := fun n => (hgraphs n).memLp
  have hP : ∀ n, MemLp (P n) 2 areaμ := fun n => (hgraphs n).memLp_weighted_deriv
  have hP0 : MemLp P0 2 areaμ := hgraph.memLp_weighted_deriv
  have hZ : ∀ n, MemLp (Z n) 2 areaμ := fun n => (hgraphs n).memLp_weighted_secondDeriv
  have hZ0 : MemLp Z0 2 areaμ := hgraph.memLp_weighted_secondDeriv
  have hAZ := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hZ hZ0 hzstrong
    hameas ha0meas (fun n => (hcoeff n).mono fun _ hx => hx.1)
    (hcoeff0.mono fun _ hx => hx.1) haConv
  have hCP := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hP hP0 hpstrong
    hcmeas hc0meas (fun n => (hcoeff n).mono fun _ hx => hx.2.1)
    (hcoeff0.mono fun _ hx => hx.2.1) hcConv
  have hER := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le hR hgraph.memLp hrstrong
    hemeas he0meas (fun n => (hcoeff n).mono fun _ hx => hx.2.2)
    (hcoeff0.mono fun _ hx => hx.2.2) heConv
  let Q : ℕ → ℝ → ℝ := fun n x => a n x * Z n x + c n x * P n x - e n x * r n x
  let Q0 : ℝ → ℝ := fun x => a0 x * Z0 x + c0 x * P0 x - e0 x * r0 x
  have hQ : ∀ n, MemLp (Q n) 2 areaμ := fun n =>
    ((hAZ.1 n).add (hCP.1 n)).sub (hER.1 n)
  have hQ0 : MemLp Q0 2 areaμ := (hAZ.2.1.add hCP.2.1).sub hER.2.1
  have hsum := weighted_operator_graph_add hAZ.2.2 hCP.2.2
  have hfull := weighted_operator_graph_sub hsum hER.2.2
  have hQstrong : Tendsto (fun n => eLpNorm (Q n - Q0) 2 areaμ) atTop (𝓝 0) := by
    simpa only [Q, Q0, Pi.add_def, Pi.sub_def] using hfull
  have hQeq (n : ℕ) : Q n =ᵐ[areaμ]
      (fun x => Real.sqrt (w x) * meridionalOperator (K n) (r n) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact weighted_operator_cancel (hwpos x hx)
  have hQeq0 : Q0 =ᵐ[areaμ]
      (fun x => Real.sqrt (w x) * weakMeridionalOperator K0 r0 p0 z0 x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact weighted_operator_cancel (hwpos x hx)
  refine ⟨fun n => (memLp_congr_ae (hQeq n)).mp (hQ n),
    (memLp_congr_ae hQeq0).mp hQ0, ?_⟩
  apply hQstrong.congr'
  refine Eventually.of_forall ?_
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [hQeq n, hQeq0] with x hx hx0
  simp only [Pi.sub_apply, hx, hx0, w]

end RicciFlowSharpEstimate.Geometry.AreaProfile
