/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization
import RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature
import RicciFlowSharpEstimate.Analysis.ClosedIntervalDerivatives
import RicciFlowSharpEstimate.Analysis.SmoothIntervalExtension

/-!
# Picone comparison for the complete area action

The algebraic identity uses the complete action and its complete polarization.
The mixed and potential terms cancel in their difference. Its smooth integral
form compares every original smooth probe with a positive reference satisfying
the actual Jacobi equation and a nonpositive meridional operator. Positivity
of the reference is required only on the physical closed interval; a smooth
extension of the quotient preserves the original probe and both derivatives.

The reference positivity and operator sign are hypotheses. No optimizer,
nonvanishing principle, or curvature-ratio threshold is asserted here.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff

/-- The exact Picone identity for arbitrary supplied function jets. Analytic
consumers must tie the jets to their actual or weak derivatives. The mixed
and potential terms of the complete density cancel only in this difference. -/
theorem weakMeridionalPicone_density_identity (K r p z u v w : ℝ → ℝ) (x : ℝ) :
    meridionalActionDensity (warp K x) (warpSlope K x) (K x)
        (r x * u x) (p x * u x + r x * v x)
        (z x * u x + 2 * p x * v x + r x * w x) -
      weakMeridionalPairingDensity K r p z
        (fun y => r y * u y ^ 2)
        (fun y => p y * u y ^ 2 + 2 * r y * u y * v y)
        (fun y => z y * u y ^ 2 + 4 * p y * u y * v y +
          2 * r y * (v y ^ 2 + u y * w y)) x =
      warp K x * (warp K x * r x * w x +
        2 * (warp K x * p x + warpSlope K x * r x) * v x) ^ 2 -
        2 * warp K x ^ 2 * r x * weakMeridionalOperator K r p z x * v x ^ 2 := by
  unfold meridionalActionDensity weakMeridionalPairingDensity weakMeridionalOperator
  ring

private theorem picone_deriv_mul (r u : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u) :
    deriv (fun y => r y * u y) = fun y => deriv r y * u y + r y * deriv u y := by
  funext x
  exact ((hr.differentiable (by simp) x).hasDerivAt.mul
    (hu.differentiable (by simp) x).hasDerivAt).deriv

private theorem picone_deriv_deriv_mul (r u : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u) :
    deriv (deriv (fun y => r y * u y)) = fun y =>
      deriv (deriv r) y * u y + 2 * deriv r y * deriv u y + r y * deriv (deriv u) y := by
  have hr1 := (contDiff_infty_iff_deriv.mp hr).2
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  rw [picone_deriv_mul r u hr hu]
  funext x
  calc
    _ = (deriv (deriv r) x * u x + deriv r x * deriv u x) +
        (deriv r x * deriv u x + r x * deriv (deriv u) x) :=
      (((hr1.differentiable (by simp) x).hasDerivAt.mul
        (hu.differentiable (by simp) x).hasDerivAt).add
        ((hr.differentiable (by simp) x).hasDerivAt.mul
          (hu1.differentiable (by simp) x).hasDerivAt)).deriv
    _ = _ := by ring

private theorem picone_deriv_mul_sq (r u : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u) :
    deriv (fun y => r y * u y ^ 2) = fun y =>
      deriv r y * u y ^ 2 + 2 * r y * u y * deriv u y := by
  have hsq : (fun y => r y * u y ^ 2) = fun y => r y * (u y * u y) := by
    funext y
    ring
  rw [hsq, picone_deriv_mul r _ hr (hu.mul hu), picone_deriv_mul u u hu hu]
  funext y
  dsimp only
  ring

private theorem picone_deriv_deriv_mul_sq (r u : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u) :
    deriv (deriv (fun y => r y * u y ^ 2)) = fun y =>
      deriv (deriv r) y * u y ^ 2 + 4 * deriv r y * u y * deriv u y +
        2 * r y * (deriv u y ^ 2 + u y * deriv (deriv u) y) := by
  have hsq : (fun y => r y * u y ^ 2) = fun y => r y * (u y * u y) := by
    funext y
    ring
  rw [hsq, picone_deriv_deriv_mul r _ hr (hu.mul hu),
    picone_deriv_deriv_mul u u hu hu, picone_deriv_mul u u hu hu]
  funext y
  dsimp only
  ring

private theorem picone_pairing_continuous (K r s : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    Continuous (weakMeridionalPairingDensity K r (deriv r) (deriv (deriv r))
      s (deriv s) (deriv (deriv s))) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr1 := hr.continuous_deriv (by simp)
  have hs1 := hs.continuous_deriv (by simp)
  have hr2 := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  have hs2 := (contDiff_infty_iff_deriv.mp hs).2.continuous_deriv (by simp)
  unfold weakMeridionalPairingDensity weakMeridionalOperator
  fun_prop

/-- The complete smooth action minus the complete pairing with the square
multiplier is the exact integrated Picone remainder. All jets are the actual
derivatives of the same smooth functions, and no moment or sign is assumed. -/
theorem meridionalAction_mul_sub_pairing_eq_picone (K r u : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u) :
    meridionalAction K (fun x => r x * u x) -
      weakMeridionalPairing K r (deriv r) (deriv (deriv r))
        (fun x => r x * u x ^ 2) (deriv (fun x => r x * u x ^ 2))
        (deriv (deriv (fun x => r x * u x ^ 2))) =
      ∫ x in (0 : ℝ)..1,
        warp K x * (warp K x * r x * deriv (deriv u) x +
          2 * (warp K x * deriv r x + warpSlope K x * r x) * deriv u x) ^ 2 -
          2 * warp K x ^ 2 * r x * meridionalOperator K r x * deriv u x ^ 2 := by
  have hA := meridionalAction_integrand_intervalIntegrable K
    (fun x => r x * u x) hK (hr.mul hu)
  have hB := (picone_pairing_continuous K r (fun x => r x * u x ^ 2)
    hK hr (hr.mul (hu.pow 2))).intervalIntegrable (μ := volume) 0 1
  unfold meridionalAction weakMeridionalPairing
  rw [← intervalIntegral.integral_sub hA hB]
  apply intervalIntegral.integral_congr
  intro x _
  rw [picone_deriv_deriv_mul r u hr hu, picone_deriv_mul r u hr hu,
    picone_deriv_deriv_mul_sq r u hr hu, picone_deriv_mul_sq r u hr hu]
  simpa only [meridionalOperator, weakMeridionalOperator] using
    weakMeridionalPicone_density_identity K r (deriv r) (deriv (deriv r))
      u (deriv u) (deriv (deriv u)) x

private theorem picone_pairing_eq_jacobi (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    weakMeridionalPairing K r (deriv r) (deriv (deriv r))
      s (deriv s) (deriv (deriv s)) =
      ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x := by
  have hflux (x : ℝ) :
      HasDerivAt (fun y => -(K y * warp K y * warpSlope K y * r y * s y) / 2)
        (weakMeridionalPairingDensity K r (deriv r) (deriv (deriv r))
          s (deriv s) (deriv (deriv s)) x -
          (warp K x * meridionalOperator K r x * meridionalOperator K s x +
            (warp K x * warpSlope K x * deriv K x / 2) * r x * s x)) x := by
    have hdK := (hK.differentiable (by simp) x).hasDerivAt
    have hdr := (hr.differentiable (by simp) x).hasDerivAt
    have hds := (hs.differentiable (by simp) x).hasDerivAt
    have hf := warp_hasDerivAt K hK.continuous x
    have hb := warpSlope_hasDerivAt K hK.continuous x
    convert (((((hdK.mul hf).mul hb).mul hdr).mul hds).neg).div_const 2 using 1
    simp only [Pi.mul_apply]
    unfold weakMeridionalPairingDensity weakMeridionalOperator meridionalOperator
    ring
  have hP := picone_pairing_continuous K r s hK.continuous hr hs
  have hf := warp_continuous K hK.continuous
  have hb := warpSlope_continuous K hK.continuous
  have hdK := hK.continuous_deriv (by simp)
  have hLr := (meridionalOperator_contDiff K r hK hr).continuous
  have hLs := (meridionalOperator_contDiff K s hK hs).continuous
  have hF : Continuous (fun x =>
      warp K x * meridionalOperator K r x * meridionalOperator K s x +
        (warp K x * warpSlope K x * deriv K x / 2) * r x * s x) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hflux x) ((hP.sub hF).intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_sub (hP.intervalIntegrable (μ := volume) 0 1)
    (hF.intervalIntegrable (μ := volume) 0 1)] at hi
  simp only [warp_zero, warp_one K hK.continuous hzero hone,
    mul_zero, zero_mul, neg_zero, zero_div, sub_self] at hi
  calc
    _ = ∫ x in (0 : ℝ)..1,
        warp K x * meridionalOperator K r x * meridionalOperator K s x +
          (warp K x * warpSlope K x * deriv K x / 2) * r x * s x :=
      sub_eq_zero.mp hi
    _ = _ := integral_meridionalOperator_pair_eq_jacobi K r s hK hr hs hzero hone

/-- A positive smooth reference with the actual Jacobi eigenvalue equation
and nonpositive meridional operator bounds the complete action of every
original smooth probe by its original weighted mass. Reference positivity
is needed only on the physical closed interval. -/
theorem meridionalAction_ge_mass_of_ground_state (C lam : ℝ) (K r : ℝ → ℝ)
    (hK : IsSmoothAreaCurvature C K) (hr : ContDiff ℝ ∞ r)
    (hrpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < r x)
    (heigen : ∀ x ∈ Icc (0 : ℝ) 1, meridionalJacobiOperator K r x = lam * r x)
    (hoperator : ∀ x ∈ Icc (0 : ℝ) 1, meridionalOperator K r x ≤ 0) :
    ∀ s : ℝ → ℝ, ContDiff ℝ ∞ s → lam * probeMass K s ≤ meridionalAction K s := by
  intro s hs
  rcases hK with ⟨hK, ⟨κ, Λ, hκ, hbox, _⟩, hzero, hone⟩
  have hKpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x :=
    fun x hx => hκ.trans_le (hbox x hx).1
  have hfnonneg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ warp K x := by
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · simpa only [← h0, warp_zero] using (le_refl (0 : ℝ))
    rcases lt_or_eq_of_le hx.2 with h1 | h1
    · exact (warp_pos_of_moments K hK.continuous hKpos hzero hone x ⟨h0, h1⟩).le
    · simpa only [h1, warp_one K hK.continuous hzero hone] using (le_refl (0 : ℝ))
  have hquot : ContDiffOn ℝ ∞ (fun x => s x / r x) (Icc (0 : ℝ) 1) :=
    hs.contDiffOn.div hr.contDiffOn (fun x hx => (hrpos x hx).ne')
  obtain ⟨u, hu, hueq⟩ := Analysis.exists_contDiff_extension_Icc
    (fun x => s x / r x) 0 1 zero_lt_one hquot
  have hru : ContDiff ℝ ∞ (fun x => r x * u x) := hr.mul hu
  have hsru : EqOn s (fun x => r x * u x) (Icc (0 : ℝ) 1) := by
    intro x hx
    dsimp only
    rw [hueq hx]
    field_simp [(hrpos x hx).ne']
  obtain ⟨hd, hdd⟩ := Analysis.eqOn_derivatives_Icc 0 1 zero_lt_one
    s (fun x => r x * u x) (hs.of_le (by simp)) (hru.of_le (by simp)) hsru
  have hA : meridionalAction K s = meridionalAction K (fun x => r x * u x) := by
    unfold meridionalAction
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    dsimp only
    rw [hsru hx', hd hx', hdd hx']
  have hB : weakMeridionalPairing K r (deriv r) (deriv (deriv r))
      (fun x => r x * u x ^ 2) (deriv (fun x => r x * u x ^ 2))
      (deriv (deriv (fun x => r x * u x ^ 2))) = lam * probeMass K s := by
    rw [picone_pairing_eq_jacobi K r (fun x => r x * u x ^ 2)
      hK hr (hr.mul (hu.pow 2)) hzero hone]
    calc
      _ = ∫ x in (0 : ℝ)..1, lam * (warp K x * s x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
        dsimp only
        rw [heigen x hx', hsru hx']
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hidentity := meridionalAction_mul_sub_pairing_eq_picone K r u hK.continuous hr hu
  rw [hB, ← hA] at hidentity
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..1,
      warp K x * (warp K x * r x * deriv (deriv u) x +
        2 * (warp K x * deriv r x + warpSlope K x * r x) * deriv u x) ^ 2 -
        2 * warp K x ^ 2 * r x * meridionalOperator K r x * deriv u x ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    have hcoeff : 0 ≤ 2 * warp K x ^ 2 * r x :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hrpos x hx).le
    have hneg : 2 * warp K x ^ 2 * r x * meridionalOperator K r x * deriv u x ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hcoeff (hoperator x hx)) (sq_nonneg _)
    exact sub_nonneg.mpr (hneg.trans (mul_nonneg (hfnonneg x hx) (sq_nonneg _)))
  linarith

end RicciFlowSharpEstimate.Geometry.AreaProfile
