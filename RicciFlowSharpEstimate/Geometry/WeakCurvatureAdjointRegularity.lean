/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjoint
import RicciFlowSharpEstimate.Analysis.WeightedGreenRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The regular part of the actual curvature adjoint -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The part of the full curvature adjoint left after its direct term
`2*f*r²*K`, using the canonical continuous momentum representative. At an
actual minimum the theorem below ties it a.e. to the original adjoint. -/
def weakCurvatureAdjointRegularPart (K r p z : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  let q := weakProbeEulerMomentum K r p z lam x / f ^ 2;
  -2 * f * q * r x - b * f * r x * p x - b ^ 2 * r x ^ 2 / 2 +
    2 * (∫ s, Analysis.unitDirichletKernel s x *
      (weakCurvatureWarpCoefficient K r p z s - lam * r s ^ 2) ∂areaμ) +
    2 * (∫ s, Analysis.unitDirichletSlopeKernel s x *
      weakCurvatureSlopeCoefficient K r p z s ∂areaμ)

private theorem ac_derivative_from_ae_limit
    {f : ℝ → ℝ} {a x b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hax : a < x) (hxb : x < b)
    (hlim : Tendsto (deriv f) (𝓝 x ⊓ ae volume) (𝓝 c)) :
    HasDerivAt f c x := by
  have hD := intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
    (f := deriv f) (a := x) (b := x) (c := c) IntervalIntegrable.refl
    (stronglyMeasurable_deriv f).aestronglyMeasurable.stronglyMeasurableAtFilter hlim
  have heq : (fun y => ∫ t in x..y, deriv f t) =ᶠ[𝓝 x] (fun y => f y - f x) := by
    filter_upwards [Ioo_mem_nhds hax hxb] with y hy
    apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    apply hf.mono
    intro t ht
    rw [uIcc_of_le (hax.trans hxb).le]
    rcases mem_uIcc.mp ht with ht | ht
    · exact ⟨hax.le.trans ht.1, ht.2.trans hy.2.le⟩
    · exact ⟨hy.1.le.trans ht.1, ht.2.trans hxb.le⟩
  have hsub : HasDerivAt (fun y => f y - f x) c x :=
    hD.congr_of_eventuallyEq heq.symm
  simpa only [sub_add_cancel] using hsub.add_const (f x)

private theorem local_ac_continuous {u : ℝ → ℝ}
    (hu : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval u a b) : ContinuousOn u (Ioo (0 : ℝ) 1) := by
  intro x hx
  have ha : x / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hb : (x + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hm : uIcc (x / 2) ((x + 1) / 2) ∈ 𝓝 x := by
    rw [uIcc_of_le (by linarith : x / 2 ≤ (x + 1) / 2)]
    exact Icc_mem_nhds (by linarith [hx.1]) (by linarith [hx.2])
  exact ((hu _ ha _ hb).continuousOn.continuousAt hm).continuousWithinAt

/-- The actual complete curvature adjoint minus its direct curvature factor
has a C¹ representative. Its first derivative has no explicit curvature term,
and its second derivative is affine in the measurable curvature with continuous
state coefficients. Every momentum, tail and derivative is tied to the minimum. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_regularPart_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let f := warp K
    let b := warpSlope K
    let P := weakProbeEulerFlux K r p z lam
    let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
    let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
    let B := weakCurvatureSlopeCoefficient K r p z
    let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
    let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
      3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
        2 * ∫ s in (0 : ℝ)..1, B s
    weakCurvatureAdjoint K r p z lam =ᵐ[areaμ]
      (fun x => 2 * f x * r x ^ 2 * K x + weakCurvatureAdjointRegularPart K r p z lam x) ∧
    ContDiffOn ℝ 1 (weakCurvatureAdjointRegularPart K r p z lam) (Ioo (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (weakCurvatureAdjointRegularPart K r p z lam) (F x) x) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval F a d) ∧
    (∀ᵐ x ∂areaμ, HasDerivAt F
      ((2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
          b x ^ 2 * r x ^ 2 / (2 * f x)) * K x +
        3 * b x ^ 2 * p x ^ 2 - 3 * b x * q x * p x +
          4 * P x * p x / f x - b x * P x * r x / f x ^ 2) x) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let P := weakProbeEulerFlux K r p z lam
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let G := fun x => ∫ s, Analysis.unitDirichletKernel s x * A s ∂areaμ
  let T := fun x => ∫ s, Analysis.unitDirichletSlopeKernel s x * B s ∂areaμ
  let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  let D0 := fun x => -2 * f x * q x * r x - b x * f x * r x * p x -
    b x ^ 2 * r x ^ 2 / 2
  let R := weakCurvatureAdjointRegularPart K r p z lam
  let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
    3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
      2 * ∫ s in (0 : ℝ)..1, B s
  obtain ⟨hrD, hrCD, hqC, hqeq, hpqAC, hsys⟩ :=
    h.probe_first_order_system_of_minimum hC hr hp hmin
  have hP := (h.probe_euler_flux_of_minimum hC hmin).2.1
  change ContinuousOn q (Ioo (0 : ℝ) 1) at hqC
  change weakMeridionalOperator K r p z =ᵐ[areaμ] q at hqeq
  change (∀ a ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval p a d ∧ AbsolutelyContinuousOnInterval q a d) at hpqAC
  change (∀ᵐ x ∂areaμ,
    HasDerivAt p ((q x - 2 * b x * p x + K x * r x) / f x) x ∧
    HasDerivAt q ((P x - K x * b x * f x * r x / 2) / f x ^ 2) x ∧
    HasDerivAt P (f x * K x * q x + K x * b x * f x * p x / 2 -
      (K x ^ 2 * f x - K x * b x ^ 2 / 2) * r x + lam * f x * r x) x) at hsys
  change AbsolutelyContinuousOnInterval P 0 1 at hP
  have hg := h.geometry_bounds hC
  obtain ⟨hfD, hbAC, hbD⟩ := h.primitive_local_regularity hC
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (b x) x) at hfD
  change (∀ a ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval b a d) at hbAC
  change (∀ᵐ x ∂areaμ, HasDerivAt b (-2 * K x) x) at hbD
  have hw := h.primitive_weak_derivatives hC
  have hfC := hg.1.mono Ioo_subset_Icc_self
  have hbC := hg.2.1.mono Ioo_subset_Icc_self
  have hfCD : ContDiffOn ℝ 1 f (Ioo (0 : ℝ) 1) :=
    hw.1.contDiffOn_one_of_continuousOn hfC hbC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x := by
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  obtain ⟨_, hAw0, hBi, _⟩ := h.curvature_coefficients_integrable hC
  have hweightm : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hweightb : ∀ᵐ x ∂areaμ, ‖x * (1 - x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  have hAw : Integrable (fun x => x * (1 - x) * A x) areaμ := by
    apply (hAw0.sub ((h.2.1.integrable_sq.bdd_mul hweightm hweightb).const_mul lam)).congr
    filter_upwards [] with x
    change x * (1 - x) * weakCurvatureWarpCoefficient K r p z x -
      lam * (x * (1 - x) * r x ^ 2) = x * (1 - x) * A x
    dsimp only [A]
    ring
  obtain ⟨_, _, hJC, hGD, hGAC, hJD⟩ :=
    Analysis.weighted_dirichlet_adjoint_local_regularity A hAw
  change ContinuousOn J (Ioo (0 : ℝ) 1) at hJC
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (J x) x) at hGD
  change (∀ a ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval G a d ∧ AbsolutelyContinuousOnInterval J a d) at hGAC
  change (∀ᵐ x ∂areaμ, HasDerivAt J (-A x) x) at hJD
  obtain ⟨_, hTAC, _, _, hTD⟩ := Analysis.slope_kernel_adjoint_absolutelyContinuous B hBi
  have hPAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) : AbsolutelyContinuousOnInterval P a d :=
    hP.mono (by simpa only [uIcc_of_le zero_le_one] using
      (ordConnected_Ioo.uIcc_subset ha hd).trans Ioo_subset_Icc_self)
  have hRAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) : AbsolutelyContinuousOnInterval R a d := by
    have hfA := (hfCD.mono (ordConnected_Ioo.uIcc_subset ha hd)).absolutelyContinuousOnInterval
    have hbA := hbAC a ha d hd
    have hrA := (hrCD.mono (ordConnected_Ioo.uIcc_subset ha hd)).absolutelyContinuousOnInterval
    have hpA := (hpqAC a ha d hd).1
    have hqA := (hpqAC a ha d hd).2
    have haux :=
      ((((hfA.const_mul (-2)).fun_mul hqA).fun_mul hrA).fun_sub
        (((hbA.fun_mul hfA).fun_mul hrA).fun_mul hpA)).fun_sub
          (((hbA.fun_mul hbA).fun_mul (hrA.fun_mul hrA)).const_mul (1 / 2 : ℝ))
    have hDA : AbsolutelyContinuousOnInterval D0 a d := by
      apply haux.congr
      intro x _
      dsimp only [D0, f, b, q, lam]
      ring
    have hTA : AbsolutelyContinuousOnInterval T a d := hTAC.mono (by
      simpa only [uIcc_of_le zero_le_one] using
        (ordConnected_Ioo.uIcc_subset ha hd).trans Ioo_subset_Icc_self)
    change AbsolutelyContinuousOnInterval (fun x => D0 x + 2 * G x + 2 * T x) a d
    exact (hDA.fun_add ((hGAC a ha d hd).1.const_mul 2)).fun_add (hTA.const_mul 2)
  have hFAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) : AbsolutelyContinuousOnInterval F a d := by
    have hs := ordConnected_Ioo.uIcc_subset ha hd
    have hfA := (hfCD.mono hs).absolutelyContinuousOnInterval
    have hbA := hbAC a ha d hd
    have hrA := (hrCD.mono hs).absolutelyContinuousOnInterval
    have hpA := (hpqAC a ha d hd).1
    have hqA := (hpqAC a ha d hd).2
    have hiA := ((hfCD.mono hs).inv
      (fun x hx => (hfpos x (hs hx)).ne')).absolutelyContinuousOnInterval
    have hFA := ((((hfA.const_mul 6).fun_mul hqA).fun_mul hpA).fun_sub
      ((hbA.fun_mul hfA).fun_mul (hpA.fun_mul hpA))).fun_sub
        (((hbA.const_mul 3).fun_mul hqA).fun_mul hrA)
    have hPB := (((hPAC a ha d hd).const_mul 2).fun_mul hrA).fun_mul hiA
    have hconst : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => 2 * ∫ s in (0 : ℝ)..1, B s) a d := by
      exact (contDiff_const : ContDiff ℝ 1
        (fun _ : ℝ => 2 * ∫ s in (0 : ℝ)..1, B s)).contDiffOn.absolutelyContinuousOnInterval
    apply (((hFA.fun_sub hPB).fun_add ((hGAC a ha d hd).2.const_mul 2)).fun_sub hconst).congr
    intro x _
    dsimp only [F]
    simp only [Pi.inv_apply, div_eq_mul_inv, pow_two]
  have hFC : ContinuousOn F (Ioo (0 : ℝ) 1) := local_ac_continuous hFAC
  have hRder : ∀ᵐ x ∂areaμ, HasDerivAt R (F x) x := by
    filter_upwards [hsys, hbD, hTD, hqeq, ae_restrict_mem measurableSet_Ioo]
      with x hx hbX hTX hqx hxI
    have hfX := hfD x hxI
    have hrX := hrD x hxI
    have hqX := hx.2.1
    have hpX := hx.1
    have hDX := ((((hfX.const_mul (-2)).fun_mul hqX).fun_mul hrX).fun_sub
      (((hbX.fun_mul hfX).fun_mul hrX).fun_mul hpX)).fun_sub
        (((hbX.pow 2).fun_mul (hrX.pow 2)).div_const 2)
    have hRR := (hDX.fun_add ((hGD x hxI).const_mul 2)).fun_add (hTX.const_mul 2)
    change HasDerivAt R _ x at hRR
    apply hRR.congr_deriv
    have hBval : B x = 4 * f x * q x * p x - K x * r x *
        (f x * p x + b x * r x) := by
      dsimp only [B, weakCurvatureSlopeCoefficient]
      rw [hqx]
    dsimp only [F]
    rw [hBval]
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [(hfpos x hxI).ne']
    ring
  have hRD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt R (F x) x := by
    have ha : x / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have hd : (x + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    apply ac_derivative_from_ae_limit (hRAC _ ha _ hd)
      (by linarith [hx.1]) (by linarith [hx.2])
    have hlim := (hFC.continuousAt (isOpen_Ioo.mem_nhds hx)).tendsto.mono_left
      (show 𝓝 x ⊓ ae volume ≤ 𝓝 x from inf_le_left)
    apply hlim.congr'
    have hae := (ae_restrict_iff' measurableSet_Ioo).mp hRder
    have hI : ∀ᶠ y in 𝓝 x ⊓ ae volume, y ∈ Ioo (0 : ℝ) 1 :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from isOpen_Ioo.mem_nhds hx).filter_mono
        inf_le_left
    filter_upwards [hae.filter_mono inf_le_right, hI] with y hy hyI
    exact (hy hyI).deriv.symm
  have hRCD : ContDiffOn ℝ 1 R (Ioo (0 : ℝ) 1) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
    refine ⟨fun x hx => (hRD x hx).differentiableAt.differentiableWithinAt, ?_⟩
    apply hFC.congr
    intro x hx
    exact (hRD x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)
  refine ⟨?_, hRCD, hRD, hFAC, ?_⟩
  · filter_upwards [hqeq] with x hx
    dsimp only [weakCurvatureAdjoint, weakCurvatureCoefficient,
      weakCurvatureAdjointRegularPart]
    rw [hx]
    ring
  · change ∀ᵐ x ∂areaμ, HasDerivAt F
      ((2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
          b x ^ 2 * r x ^ 2 / (2 * f x)) * K x +
        3 * b x ^ 2 * p x ^ 2 - 3 * b x * q x * p x +
          4 * P x * p x / f x - b x * P x * r x / f x ^ 2) x
    filter_upwards [hsys, hbD, hJD, hqeq, ae_restrict_mem measurableSet_Ioo]
      with x hx hbX hJX hqx hxI
    have hfX := hfD x hxI
    have hrX := hrD x hxI
    have hpX := hx.1
    have hqX := hx.2.1
    have hPX := hx.2.2
    have hfne := (hfpos x hxI).ne'
    have hFX := ((((((hfX.const_mul 6).fun_mul hqX).fun_mul hpX).fun_sub
      ((hbX.fun_mul hfX).fun_mul (hpX.pow 2))).fun_sub
        (((hbX.const_mul 3).fun_mul hqX).fun_mul hrX)).fun_sub
          (((hPX.const_mul 2).fun_mul hrX).div hfX hfne)).fun_add (hJX.const_mul 2)
    have hFF := hFX.sub_const (2 * ∫ s in (0 : ℝ)..1, B s)
    have hzval : z x = (q x - 2 * b x * p x + K x * r x) / f x := by
      apply (eq_div_iff hfne).mpr
      dsimp only [weakMeridionalOperator] at hqx
      change f x * z x + 2 * b x * p x - K x * r x = q x at hqx
      nlinarith only [hqx]
    change HasDerivAt F _ x at hFF
    apply hFF.congr_deriv
    have hAval : A x = q x ^ 2 + 2 * f x * q x * z x -
        K x * b x * r x * p x + K x ^ 2 * r x ^ 2 - lam * r x ^ 2 := by
      dsimp only [A, weakCurvatureWarpCoefficient]
      rw [hqx]
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hAval, hzval]
    field_simp [hfne]
    ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
