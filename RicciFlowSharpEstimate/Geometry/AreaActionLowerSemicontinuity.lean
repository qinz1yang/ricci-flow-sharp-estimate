/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakAreaAction
import RicciFlowSharpEstimate.Geometry.AreaDerivativeProductLimit
import RicciFlowSharpEstimate.Geometry.AreaCurvatureProductLimits
import RicciFlowSharpEstimate.Analysis.L2WeakLowerSemicontinuity

/-!
# Lower semicontinuity of the complete area action

Both positive squares are kept separately. The terms linear in curvature
are passed to their actual limits, without asserting full-remainder
continuity or excluding concentration of positive operator energy.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem action_eq_sqrt_squares
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
      ((∫ x, K x * warpSlope K x * warp K x * r x * p x ∂areaμ) +
        (1 / 2 : ℝ) * ∫ x, K x * (warpSlope K x) ^ 2 * (r x) ^ 2 ∂areaμ) := by
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
  ring

/-- The literal complete action is lower semicontinuous in the area graph
topology on normalized smooth sublevels. Both positive squares are treated
weakly; the two curvature-linear terms converge through actual L¹ tests. -/
theorem weak_factors_and_action_liminf_of_area_limits
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
        (𝓝 (∫ x, K0 x * v x ∂areaμ)))
    (hz : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x,
        (x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x,
          (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) :
    (∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x,
        (Real.sqrt (warp (K n) x) * meridionalOperator (K n) (r n) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x,
          (Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x) * v x ∂areaμ))) ∧
    (∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x,
        (Real.sqrt (warp (K n) x) * (K n x * r n x)) * v x ∂areaμ)
        atTop (𝓝 (∫ x,
          (Real.sqrt (warp K0 x) * (K0 x * r0 x)) * v x ∂areaμ))) ∧
      weakMeridionalAction K0 r0 p0 z0 ≤
        liminf (fun n => meridionalAction (K n) (r n)) atTop := by
  have hCurv := curvature_action_pairings_tendsto K r K0 r0 p0 z0 lo hi B hlo
    hK hr hbox hzero hone hmass hA hgraph hstrong hrpoint hppoint hfpoint hbpoint
    hf0 hb0 hK0 hK0box hweak
  have hPot := hCurv.1
  have hDer := weak_derivative_part_of_area_limits K r K0 r0 p0 z0 lo hi B hlo
    hK hr hbox hzero hone hmass hA hgraph
    (fun x hx => hfpoint x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => hbpoint x ⟨hx.1.le, hx.2.le⟩) hppoint hz
  let F : ℕ → ℝ → ℝ := fun n x => Real.sqrt (warp (K n) x) * meridionalOperator (K n) (r n) x
  let F0 : ℝ → ℝ := fun x => Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x
  let V : ℕ → ℝ → ℝ := fun n x => Real.sqrt (warp (K n) x) * (K n x * r n x)
  let V0 : ℝ → ℝ := fun x => Real.sqrt (warp K0 x) * (K0 x * r0 x)
  have hF (n : ℕ) : MemLp (F n) 2 areaμ := by
    have hsub : MemLp (fun x => Real.sqrt (warp (K n) x) *
        (warp (K n) x * deriv (deriv (r n)) x + 2 * warpSlope (K n) x * deriv (r n) x) -
        Real.sqrt (warp (K n) x) * (K n x * r n x)) 2 areaμ :=
      (hDer.1 n).sub (hPot.1 n)
    simpa only [F, meridionalOperator, mul_sub] using hsub
  have hF0 : MemLp F0 2 areaμ := by
    have hsub : MemLp (fun x => Real.sqrt (warp K0 x) *
        (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x) -
        Real.sqrt (warp K0 x) * (K0 x * r0 x)) 2 areaμ := hDer.2.1.sub hPot.2.1
    simpa only [F0, weakMeridionalOperator, mul_sub] using hsub
  have hFweak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, F n x * v x ∂areaμ) atTop (𝓝 (∫ x, F0 x * v x ∂areaμ)) := by
    intro v
    have hn (n : ℕ) : (∫ x, F n x * v x ∂areaμ) =
        (∫ x, (Real.sqrt (warp (K n) x) *
          (warp (K n) x * deriv (deriv (r n)) x +
            2 * warpSlope (K n) x * deriv (r n) x)) * v x ∂areaμ) -
        (∫ x, V n x * v x ∂areaμ) := by
      have hiD : Integrable (fun x => (Real.sqrt (warp (K n) x) *
          (warp (K n) x * deriv (deriv (r n)) x +
            2 * warpSlope (K n) x * deriv (r n) x)) * v x) areaμ :=
        (hDer.1 n).integrable_mul (Lp.memLp v)
      have hiV : Integrable (fun x => V n x * v x) areaμ :=
        (hPot.1 n).integrable_mul (Lp.memLp v)
      rw [← integral_sub hiD hiV]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp [F, V, meridionalOperator]; ring)
    have h0 : (∫ x, F0 x * v x ∂areaμ) =
        (∫ x, (Real.sqrt (warp K0 x) *
          (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) * v x ∂areaμ) -
        (∫ x, V0 x * v x ∂areaμ) := by
      have hiD : Integrable (fun x => (Real.sqrt (warp K0 x) *
          (warp K0 x * z0 x + 2 * warpSlope K0 x * p0 x)) * v x) areaμ :=
        hDer.2.1.integrable_mul (Lp.memLp v)
      have hiV : Integrable (fun x => V0 x * v x) areaμ :=
        hPot.2.1.integrable_mul (Lp.memLp v)
      rw [← integral_sub hiD hiV]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp [F0, V0, weakMeridionalOperator]; ring)
    simpa only [hn, h0] using (hDer.2.2 v).sub (hPot.2.2 v)
  have hhi : 0 ≤ hi := hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans (hbox 0 0 (by norm_num)).2)
  have hfB (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ warp (K n) x ∧ warp (K n) x ≤ hi * (x * (1 - x)) := by
    have h := warp_bounds_of_curvature_bounds (K n) (hK n) lo hi (hbox n)
      (hzero n) (hone n) x hx
    refine ⟨(mul_nonneg (mul_nonneg hlo.le hx.1) (sub_nonneg.mpr hx.2)).trans h.1, ?_⟩
    simpa only [mul_assoc] using h.2
  have hbB (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |warpSlope (K n) x| ≤ 2 :=
    abs_warpSlope_le_two (K n) (hK n)
      (fun y hy => hlo.le.trans (hbox n y hy).1) (hzero n) x hx
  have hf0B : ∀ᵐ x ∂areaμ, 0 ≤ warp K0 x ∧ warp K0 x ≤ hi * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨ge_of_tendsto' (hfpoint x ⟨hx.1.le, hx.2.le⟩)
      (fun n => (hfB n x ⟨hx.1.le, hx.2.le⟩).1),
      le_of_tendsto' (hfpoint x ⟨hx.1.le, hx.2.le⟩)
        (fun n => (hfB n x ⟨hx.1.le, hx.2.le⟩).2)⟩
  have hb0B : ∀ᵐ x ∂areaμ, |warpSlope K0 x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact le_of_tendsto' (hbpoint x ⟨hx.1.le, hx.2.le⟩).abs
      (fun n => hbB n x ⟨hx.1.le, hx.2.le⟩)
  let s : ℕ → ℝ := fun n =>
    (∫ x, K n x * warpSlope (K n) x * warp (K n) x * r n x * deriv (r n) x ∂areaμ) +
      (1 / 2 : ℝ) * (∫ x, K n x * (warpSlope (K n) x) ^ 2 * r n x ^ 2 ∂areaμ)
  let s0 : ℝ :=
    (∫ x, K0 x * warpSlope K0 x * warp K0 x * r0 x * p0 x ∂areaμ) +
      (1 / 2 : ℝ) * (∫ x, K0 x * (warpSlope K0 x) ^ 2 * r0 x ^ 2 ∂areaμ)
  have hs : Tendsto s atTop (𝓝 s0) := hCurv.2.1.2.add (hCurv.2.2.2.const_mul (1 / 2 : ℝ))
  have hEq (n : ℕ) : meridionalAction (K n) (r n) =
      (∫ x, F n x ^ 2 ∂areaμ) + (∫ x, V n x ^ 2 ∂areaμ) - s n := by
    have hKn : ∀ᵐ x ∂areaμ, 0 ≤ K n x ∧ K n x ≤ hi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ⟨hlo.le.trans (hbox n x ⟨hx.1.le, hx.2.le⟩).1,
        (hbox n x ⟨hx.1.le, hx.2.le⟩).2⟩
    have hfn : ∀ᵐ x ∂areaμ, 0 ≤ warp (K n) x ∧ warp (K n) x ≤ hi * (x * (1 - x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hfB n x ⟨hx.1.le, hx.2.le⟩
    have hbn : ∀ᵐ x ∂areaμ, |warpSlope (K n) x| ≤ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hbB n x ⟨hx.1.le, hx.2.le⟩
    simpa only [weakMeridionalAction_deriv, weakMeridionalOperator, meridionalOperator, F, V, s]
      using action_eq_sqrt_squares (K n) (r n) (deriv (r n)) (deriv (deriv (r n))) hi
        (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)) hhi (hK n).aestronglyMeasurable
        (warp_continuous (K n) (hK n)).aestronglyMeasurable
        (warpSlope_continuous (K n) (hK n)).aestronglyMeasurable hKn hfn hbn
  have hEq0 : weakMeridionalAction K0 r0 p0 z0 =
      (∫ x, F0 x ^ 2 ∂areaμ) + (∫ x, V0 x ^ 2 ∂areaμ) - s0 :=
    action_eq_sqrt_squares K0 r0 p0 z0 hi hgraph hhi hK0
      ((hf0.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
      ((hb0.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
      hK0box hf0B hb0B
  have hEvent : ∀ a < weakMeridionalAction K0 r0 p0 z0,
      ∀ᶠ n in atTop, a < meridionalAction (K n) (r n) := by
    intro a ha
    rw [hEq0] at ha
    have h := Analysis.eventually_lt_sum_integral_sq_sub_of_weak_L2
      hF hF0 hPot.1 hPot.2.1 hFweak hPot.2.2 hs ha
    change ∀ᶠ n in atTop,
      a < (∫ x, F n x ^ 2 ∂areaμ) + (∫ x, V n x ^ 2 ∂areaμ) - s n at h
    simpa only [← hEq] using h
  have hUpper : IsBoundedUnder (· ≤ ·) atTop (fun n => meridionalAction (K n) (r n)) :=
    ⟨B, eventually_map.mpr (Eventually.of_forall hA)⟩
  have hLower : IsBoundedUnder (· ≥ ·) atTop (fun n => meridionalAction (K n) (r n)) := by
    refine ⟨weakMeridionalAction K0 r0 p0 z0 - 1, eventually_map.mpr ?_⟩
    exact (hEvent _ (by linarith)).mono (fun _ h => h.le)
  exact ⟨hFweak, hPot.2.2, (le_liminf_iff hUpper.isCoboundedUnder_ge hLower).mpr hEvent⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
