/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvaturePoleLimits
import RicciFlowSharpEstimate.Geometry.WeakCurvatureZeroTracePole
import RicciFlowSharpEstimate.Analysis.ClampedPoleAsymptotics

/-! # Both physical curvature pole limits of the same signed zero minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem reflect_right_zero :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 (1 - 0)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    change 1 - x < 1
    linarith

private theorem reflect_left_one :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x < 1 at hx
    change 0 < 1 - x
    exact sub_pos.mpr hx

private theorem exists_limit_of_obstacle_cases
    {α : Type*} {l : Filter α} {K : α → ℝ} {lo hi h0 h1 : ℝ}
    (hs : ((0 < h0 ∨ h0 = 0 ∧ 0 < h1) → ∀ᶠ x in l, K x = lo) ∧
      ((h0 < 0 ∨ h0 = 0 ∧ h1 ≤ 0) → ∀ᶠ x in l, K x = hi)) :
    ∃ k : ℝ, Tendsto K l (𝓝 k) := by
  rcases lt_trichotomy h0 0 with hn | hz | hp
  · exact ⟨hi, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (hs.2 (Or.inl hn)))⟩
  · by_cases hh : 0 < h1
    · exact ⟨lo, tendsto_const_nhds.congr'
        (Filter.EventuallyEq.symm (hs.1 (Or.inr ⟨hz, hh⟩)))⟩
    · exact ⟨hi, tendsto_const_nhds.congr'
        (Filter.EventuallyEq.symm (hs.2 (Or.inr ⟨hz, le_of_not_gt hh⟩)))⟩
  · exact ⟨lo, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (hs.1 (Or.inl hp)))⟩

private theorem cancelled_quotient_diverges {H D : ℝ → ℝ} {q : ℝ} (hq : q ≠ 0)
    (hH : Tendsto (fun x => H x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (-3 * q ^ 2 / 8)))
    (hD : Tendsto (fun x => D x / x ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (q ^ 2 / 4))) :
    Tendsto (fun x => -H x / D x) (𝓝[>] (0 : ℝ)) atTop := by
  have hδ : q ^ 2 / 4 ≠ 0 := div_ne_zero (pow_ne_zero 2 hq) (by norm_num)
  have hDn : ∀ᶠ x in 𝓝[>] (0 : ℝ), D x ≠ 0 := by
    filter_upwards [hD.eventually (isOpen_compl_singleton.mem_nhds hδ)] with x hx
    intro he
    exact hx (by simp only [he, zero_div, mem_singleton_iff])
  have hconst : -(-3 * q ^ 2 / 8) / (q ^ 2 / 4) = (3 : ℝ) / 2 := by
    field_simp [hq]
    norm_num
  have hh := hH.neg.div hD hδ
  rw [hconst] at hh
  have hcoeff : Tendsto (fun x => (-H x / D x) * x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((3 : ℝ) / 2)) := by
    apply hh.congr'
    filter_upwards [hDn, self_mem_nhdsWithin] with x hDx hx
    change 0 < x at hx
    change (-(H x / x ^ 2)) / (D x / x ^ 3) = (-H x / D x) * x
    field_simp [hDx, hx.ne']
  have ht := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 3 / 2)
    hcoeff tendsto_inv_nhdsGT_zero
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  change ((-H x / D x) * x) * x⁻¹ = -H x / D x
  simp only [mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]

/-- One actual minimum, box and multiplier have finite limits of the same
boxed curvature at both physical poles. Zero probe traces give the derived
quadratic remainder and eventual obstacle saturation, including all lower-
order trace cases and doubly cancelling quotient divergence. -/
theorem IsRecoverableAreaCompetitor.exists_curvature_pole_limits_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ t : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < C * κ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C * κ) ∧
      (let Z := fun x => weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ))
       Integrable Z areaμ ∧ Integrable (fun x => Z x * K x) areaμ ∧
       (∀ᵐ x ∂areaμ, (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x)) ∧
       (∫ x, Z x * K x ∂areaμ) = 0 ∧
       (∫ x, max (Z x) 0 ∂areaμ) = C * (∫ x, max (-Z x) 0 ∂areaμ) ∧
       (∫ x, weakCurvatureAdjoint K r p z 0 x ∂areaμ) =
         (C - 1) * (∫ x, max (-Z x) 0 ∂areaμ)) ∧
      let H := fun x => weakCurvatureAdjointRegularPart K r p z 0 x - t * (x - 1 / 2)
      let D := fun x => 2 * warp K x * r x ^ 2
      let Kc := fun x => if r x = 0 then max κ (min (C * κ) (K x))
        else max κ (min (C * κ) (-H x / D x))
      let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
      let q := fun x => weakProbeEulerMomentum K r p z 0 x / warp K x ^ 2
      let A := weakCurvatureWarpCoefficient K r p z
      let B := weakCurvatureSlopeCoefficient K r p z
      Kc =ᵐ[areaμ] K ∧ (∀ x : ℝ, κ ≤ Kc x ∧ Kc x ≤ C * κ) ∧
      (∀ c ∈ Ioo (0 : ℝ) 1, r c = 0 →
        p c ≠ 0 ∧
        (∃ kl kr : ℝ, Tendsto Kc (𝓝[<] c) (𝓝 kl) ∧ Tendsto Kc (𝓝[>] c) (𝓝 kr)) ∧
        (H c = 0 → deriv H c = 0 →
          let f := warp K c
          let b := warpSlope K c
          let qc := weakProbeEulerMomentum K r p z 0 c / f ^ 2
          let P := weakProbeEulerFlux K r p z 0 c
          let α := 2 * f * p c ^ 2
          let β := 3 * b ^ 2 * p c ^ 2 - 3 * b * qc * p c + 4 * P * p c / f
          Tendsto Kc (𝓝[≠] c) (𝓝 (max κ (min (C * κ) (-β / (3 * α))))))) ∧
      ∃ qL qR : ℝ,
        Tendsto (fun x => q x + r x * (2 - warpSlope K x) / (2 * warp K x))
          (𝓝[>] 0) (𝓝 qL) ∧
        Tendsto (fun x => q x + r x * (2 + warpSlope K x) / (2 * warp K x))
          (𝓝[<] 1) (𝓝 qR) ∧
        (R 0 ≠ 0 → ∃ k : ℝ, Tendsto Kc (𝓝[>] 0) (𝓝 k)) ∧
        (R 1 ≠ 0 → ∃ k : ℝ, Tendsto Kc (𝓝[<] 1) (𝓝 k)) ∧
        (R 0 ≠ 0 → t = 4 * R 0 ^ 2 →
          let L := -6 * R 0 * qL + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          Tendsto Kc (𝓝[>] 0) (𝓝 (max κ (min (C * κ) (-L / (5 * R 0 ^ 2)))))) ∧
        (R 1 ≠ 0 → t = -4 * R 1 ^ 2 →
          let L := 6 * R 1 * qR - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          Tendsto Kc (𝓝[<] 1) (𝓝 (max κ (min (C * κ) (L / (5 * R 1 ^ 2)))))) ∧
        (R 0 = 0 →
          let LL := 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          qL ≠ 0 ∧ Tendsto q (𝓝[>] 0) (𝓝 qL) ∧
          Tendsto p (𝓝[>] 0) (𝓝 (qL / 4)) ∧
          Tendsto (fun x => r x / x) (𝓝[>] 0) (𝓝 (qL / 4)) ∧
          (∀ᶠ x in 𝓝[>] (0 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / x ^ 3) (𝓝[>] 0) (𝓝 (qL ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[>] (0 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qL ^ 2 / 4)) ∧
          Tendsto (fun x => (H x - t / 2 - LL * x) / x ^ 2) (𝓝[>] 0)
            (𝓝 (-3 * qL ^ 2 / 8)) ∧
          ((0 < t / 2 ∨ t / 2 = 0 ∧ 0 < LL) → ∀ᶠ x in 𝓝[>] (0 : ℝ), Kc x = κ) ∧
          ((t / 2 < 0 ∨ t / 2 = 0 ∧ LL ≤ 0) → ∀ᶠ x in 𝓝[>] (0 : ℝ), Kc x = C * κ) ∧
          (t = 0 → LL = 0 → Tendsto (fun x => -H x / D x) (𝓝[>] (0 : ℝ)) atTop)) ∧
        (R 1 = 0 →
          let LR := -2 * (∫ s in (0 : ℝ)..1, s * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          qR ≠ 0 ∧ Tendsto q (𝓝[<] 1) (𝓝 qR) ∧
          Tendsto p (𝓝[<] 1) (𝓝 (-qR / 4)) ∧
          Tendsto (fun x => r x / (1 - x)) (𝓝[<] 1) (𝓝 (qR / 4)) ∧
          (∀ᶠ x in 𝓝[<] (1 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / (1 - x) ^ 3) (𝓝[<] 1) (𝓝 (qR ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[<] (1 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qR ^ 2 / 4)) ∧
          Tendsto (fun x => (H x + t / 2 + LR * (1 - x)) / (1 - x) ^ 2) (𝓝[<] 1)
            (𝓝 (-3 * qR ^ 2 / 8)) ∧
          ((0 < -t / 2 ∨ -t / 2 = 0 ∧ 0 < -LR) → ∀ᶠ x in 𝓝[<] (1 : ℝ), Kc x = κ) ∧
          ((-t / 2 < 0 ∨ -t / 2 = 0 ∧ -LR ≤ 0) →
            ∀ᶠ x in 𝓝[<] (1 : ℝ), Kc x = C * κ) ∧
          (t = 0 → LR = 0 → Tendsto (fun x => -H x / D x) (𝓝[<] (1 : ℝ)) atTop)) ∧
        ∃ kL kR : ℝ, Tendsto Kc (𝓝[>] 0) (𝓝 kL) ∧ Tendsto Kc (𝓝[<] 1) (𝓝 kR) := by
  obtain ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale, hKae, hKbox, hnodes,
      qL, qR, hQL, hQR, hKL, hKR, hSL, hSR⟩ :=
    h.exists_curvature_pole_limits_at_nonzero_traces_of_minimum hC hr hp hzero hmin
  let f := warp K
  let H := fun x => weakCurvatureAdjointRegularPart K r p z 0 x - t * (x - 1 / 2)
  let D := fun x => 2 * f x * r x ^ 2
  let Kc := fun x => if r x = 0 then max κ (min (C * κ) (K x))
    else max κ (min (C * κ) (-H x / D x))
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let A := weakCurvatureWarpCoefficient K r p z
  let B := weakCurvatureSlopeCoefficient K r p z
  let LL := 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  let LR := -2 * (∫ s in (0 : ℝ)..1, s * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  have hQuad0 := h.curvature_adjoint_zero_trace_quadratic_pole_rates_of_minimum
    hC.le hr hp hmin
  dsimp only at hQuad0
  rw [hzero] at hQuad0
  simp only [zero_mul, sub_zero] at hQuad0
  obtain ⟨qL', qR', hQL', hQR', hQuad⟩ := hQuad0
  have heL : qL' = qL := tendsto_nhds_unique hQL' hQL
  have heR : qR' = qR := tendsto_nhds_unique hQR' hQR
  subst qL'
  subst qR'
  have hState0 := h.probe_zero_trace_leading_rates_of_minimum hC.le hr hp hmin
  dsimp only at hState0
  rw [hzero] at hState0
  obtain ⟨qA, qB, hQA, hQB, hStateL, hStateR⟩ := hState0
  have heA : qA = qL := tendsto_nhds_unique hQA hQL
  have heB : qB = qR := tendsto_nhds_unique hQB hQR
  subst qA
  subst qB
  have hlohi : κ ≤ C * κ := (hκ2.trans h2hi).le
  have hLeftSat (hR0 : R 0 = 0) :
      ((0 < t / 2 ∨ t / 2 = 0 ∧ 0 < LL) → ∀ᶠ x in 𝓝[>] (0 : ℝ), Kc x = κ) ∧
      ((t / 2 < 0 ∨ t / 2 = 0 ∧ LL ≤ 0) → ∀ᶠ x in 𝓝[>] (0 : ℝ), Kc x = C * κ) := by
    have hc := (hQuad t).1 hR0
    have hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        Kc x = max κ (min (C * κ) (-H x / D x)) := by
      filter_upwards [hc.2.1] with x hx
      dsimp only [Kc]
      rw [ite_eq_right hx]
    exact Analysis.eventually_eq_obstacle_of_negative_quadratic_remainder hlohi
      (by nlinarith only [sq_pos_of_ne_zero hc.1] : -3 * qL ^ 2 / 8 < 0)
      (div_pos (sq_pos_of_ne_zero hc.1) (by norm_num)) hc.2.2.2.2 hc.2.2.1 hclip
  let HR := fun x => H (1 - x)
  let DR := fun x => D (1 - x)
  let KR := fun x => Kc (1 - x)
  have hRightRem (hR1 : R 1 = 0) :
      Tendsto (fun x => (HR x - (-t / 2) - (-LR) * x) / x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (-3 * qR ^ 2 / 8)) := by
    have hc := (hQuad t).2 hR1
    apply (hc.2.2.2.2.comp reflect_right_zero).congr'
    filter_upwards [] with x
    change (H (1 - x) + t / 2 + LR * (1 - (1 - x))) / (1 - (1 - x)) ^ 2 = _
    rw [sub_sub_cancel]
    dsimp only [HR]
    ring
  have hRightD (hR1 : R 1 = 0) :
      Tendsto (fun x => DR x / x ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (qR ^ 2 / 4)) := by
    simpa only [DR, Function.comp_def, sub_sub_cancel] using
      ((hQuad t).2 hR1).2.2.1.comp reflect_right_zero
  have hRightSat (hR1 : R 1 = 0) :
      ((0 < -t / 2 ∨ -t / 2 = 0 ∧ 0 < -LR) → ∀ᶠ x in 𝓝[<] (1 : ℝ), Kc x = κ) ∧
      ((-t / 2 < 0 ∨ -t / 2 = 0 ∧ -LR ≤ 0) →
        ∀ᶠ x in 𝓝[<] (1 : ℝ), Kc x = C * κ) := by
    have hc := (hQuad t).2 hR1
    have hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        KR x = max κ (min (C * κ) (-HR x / DR x)) := by
      filter_upwards [reflect_right_zero.eventually hc.2.1] with x hx
      dsimp only [KR, Kc, HR, DR]
      rw [ite_eq_right hx]
    have hs := Analysis.eventually_eq_obstacle_of_negative_quadratic_remainder hlohi
      (by nlinarith only [sq_pos_of_ne_zero hc.1] : -3 * qR ^ 2 / 8 < 0)
      (div_pos (sq_pos_of_ne_zero hc.1) (by norm_num)) (hRightRem hR1) (hRightD hR1) hclip
    constructor
    · intro hh
      simpa only [KR, Function.comp_def, sub_sub_cancel] using
        reflect_left_one.eventually (hs.1 hh)
    · intro hh
      simpa only [KR, Function.comp_def, sub_sub_cancel] using
        reflect_left_one.eventually (hs.2 hh)
  refine ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale, hKae, hKbox, hnodes,
    qL, qR, hQL, hQR, hKL, hKR, hSL, hSR, ?_, ?_, ?_⟩
  · intro hR0
    have hs := hStateL hR0
    have hc := (hQuad t).1 hR0
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2, (hLeftSat hR0).1, (hLeftSat hR0).2, ?_⟩
    intro ht hLL
    change LL = 0 at hLL
    have ht2 : t / 2 = 0 := by rw [ht]; norm_num
    have hrem : Tendsto (fun x => H x / x ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (-3 * qL ^ 2 / 8)) := by
      have hh := hc.2.2.2.2
      change Tendsto (fun x => (H x - t / 2 - LL * x) / x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (-3 * qL ^ 2 / 8)) at hh
      simpa only [ht2, hLL, zero_mul, sub_zero] using hh
    exact cancelled_quotient_diverges hc.1 hrem hc.2.2.1
  · intro hR1
    have hs := hStateR hR1
    have hc := (hQuad t).2 hR1
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2, (hRightSat hR1).1, (hRightSat hR1).2, ?_⟩
    intro ht hLR
    change LR = 0 at hLR
    have ht2 : -t / 2 = 0 := by rw [ht]; norm_num
    have hrem : Tendsto (fun x => HR x / x ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (-3 * qR ^ 2 / 8)) := by
      simpa only [ht2, hLR, neg_zero, zero_mul, sub_zero] using hRightRem hR1
    have hh := (cancelled_quotient_diverges hc.1 hrem (hRightD hR1)).comp reflect_left_one
    simpa only [HR, DR, Function.comp_def, sub_sub_cancel] using hh
  · have hleft : ∃ k : ℝ, Tendsto Kc (𝓝[>] (0 : ℝ)) (𝓝 k) := by
      by_cases hR0 : R 0 = 0
      · exact exists_limit_of_obstacle_cases (hLeftSat hR0)
      · exact hKL hR0
    have hright : ∃ k : ℝ, Tendsto Kc (𝓝[<] (1 : ℝ)) (𝓝 k) := by
      by_cases hR1 : R 1 = 0
      · exact exists_limit_of_obstacle_cases (hRightSat hR1)
      · exact hKR hR1
    obtain ⟨kL, hkL⟩ := hleft
    obtain ⟨kR, hkR⟩ := hright
    exact ⟨kL, kR, hkL, hkR⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
