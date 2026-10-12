/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionVariation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Weighted probe mass and the meridional Rayleigh quotient

The quotient uses the complete action and the mass of the same actual probe.
Its stationary equation has the Rayleigh quotient as its eigenvalue. The
normalized equation has the action as eigenvalue; a zero mode requires zero
action. No extremizer or nonzero eigenfunction is constructed here.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff Topology

/-- The weighted mass of a probe in the original normalized area coordinate. -/
def probeMass (K r : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2

/-- The complete meridional action divided by the mass of the same probe. -/
def rayleighQuotient (K r : ℝ → ℝ) : ℝ :=
  meridionalAction K r / probeMass K r

/-- The exact mass variation of an affine probe, including the quadratic term. -/
theorem probeMass_add_mul (K r s : ℝ → ℝ) (hK : Continuous K)
    (hr : Continuous r) (hs : Continuous s) (t : ℝ) :
    probeMass K (fun x => r x + t * s x) = probeMass K r +
      2 * t * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) + t ^ 2 * probeMass K s := by
  have hf := warp_continuous K hK
  have hF : Continuous (fun x => warp K x * r x ^ 2) := hf.mul (hr.pow 2)
  have hG : Continuous (fun x => warp K x * s x * r x) := (hf.mul hs).mul hr
  have hT : Continuous (fun x => warp K x * s x ^ 2) := hf.mul (hs.pow 2)
  unfold probeMass
  calc
    (∫ x in (0 : ℝ)..1, warp K x * (r x + t * s x) ^ 2) =
        ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2 +
          (2 * t) * (warp K x * s x * r x) + t ^ 2 * (warp K x * s x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((hF.intervalIntegrable 0 1).add ((hG.intervalIntegrable 0 1).const_mul (2 * t)))
        ((hT.intervalIntegrable 0 1).const_mul (t ^ 2)),
        intervalIntegral.integral_add (hF.intervalIntegrable 0 1)
          ((hG.intervalIntegrable 0 1).const_mul (2 * t))]
      simp only [intervalIntegral.integral_const_mul]

/-- The derivative of the actual mass along an affine probe variation. -/
theorem probeMass_hasDerivAt (K r s : ℝ → ℝ) (hK : Continuous K)
    (hr : Continuous r) (hs : Continuous s) :
    HasDerivAt (fun t => probeMass K (fun x => r x + t * s x))
      (2 * ∫ x in (0 : ℝ)..1, warp K x * s x * r x) 0 := by
  have heq : (fun t => probeMass K (fun x => r x + t * s x)) =
      fun t => probeMass K r +
        2 * t * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) + t ^ 2 * probeMass K s := by
    funext t
    exact probeMass_add_mul K r s hK hr hs t
  rw [heq]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
    (∫ x in (0 : ℝ)..1, warp K x * s x * r x)).const_add (probeMass K r) |>.add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (probeMass K s)) using 1
  · funext t
    rfl
  · norm_num

/-- The quotient derivative is the weighted pairing with the actual Euler
residual, divided by the mass of the probe. -/
theorem rayleighQuotient_hasDerivAt (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : probeMass K r ≠ 0) :
    HasDerivAt (fun t => rayleighQuotient K (fun x => r x + t * s x))
      (2 / probeMass K r * (∫ x in (0 : ℝ)..1, warp K x * s x *
        (meridionalJacobiOperator K r x - rayleighQuotient K r * r x))) 0 := by
  have hA := meridionalAction_hasDerivAt K r s hK hr hs hzero hone
  have hM := probeMass_hasDerivAt K r s hK.continuous hr.continuous hs.continuous
  have hm : probeMass K (fun x => r x + (0 : ℝ) * s x) ≠ 0 := by
    simpa only [zero_mul, add_zero] using hmass
  have hQ : HasDerivAt (fun t => rayleighQuotient K (fun x => r x + t * s x))
      (((2 * ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) *
          probeMass K r -
        meridionalAction K r * (2 * ∫ x in (0 : ℝ)..1, warp K x * s x * r x)) /
          probeMass K r ^ 2) 0 := by
    simpa only [rayleighQuotient, zero_mul, add_zero] using hA.fun_div hM hm
  have hf := warp_continuous K hK.continuous
  have hJ := (meridionalJacobiOperator_contDiff K r hK hr).continuous
  have hLeft : Continuous (fun x => warp K x * s x * meridionalJacobiOperator K r x) :=
    (hf.mul hs.continuous).mul hJ
  have hRight : Continuous (fun x => warp K x * s x * r x) :=
    (hf.mul hs.continuous).mul hr.continuous
  have hPair : (∫ x in (0 : ℝ)..1, warp K x * s x *
      (meridionalJacobiOperator K r x - rayleighQuotient K r * r x)) =
      (∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) -
        rayleighQuotient K r * (∫ x in (0 : ℝ)..1, warp K x * s x * r x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x -
          rayleighQuotient K r * (warp K x * s x * r x) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hLeft.intervalIntegrable 0 1)
          ((hRight.intervalIntegrable 0 1).const_mul (rayleighQuotient K r)),
          intervalIntegral.integral_const_mul]
  convert hQ using 1
  rw [hPair]
  unfold rayleighQuotient
  field_simp [hmass]

/-- Smooth stationarity of the complete Rayleigh quotient is exactly its
fourth-order eigen-equation, including both physical endpoints. -/
theorem rayleighQuotient_stationary_iff (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : 0 < probeMass K r) :
    (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      deriv (fun t => rayleighQuotient K (fun x => r x + t * s x)) 0 = 0) ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        meridionalJacobiOperator K r x = rayleighQuotient K r * r x := by
  let e := fun x => meridionalJacobiOperator K r x - rayleighQuotient K r * r x
  have hJ := meridionalJacobiOperator_contDiff K r hK hr
  have he : ContDiff ℝ ∞ e := hJ.sub (contDiff_const.mul hr)
  constructor
  · intro hstat
    have h := hstat e he
    rw [(rayleighQuotient_hasDerivAt K r e hK hr he hzero hone hmass.ne').deriv] at h
    have hsq : probeMass K e = 0 := by
      have heq : (∫ x in (0 : ℝ)..1, warp K x * e x *
          (meridionalJacobiOperator K r x - rayleighQuotient K r * r x)) =
          probeMass K e := by
        unfold probeMass
        apply intervalIntegral.integral_congr
        intro x _
        dsimp [e]
        ring
      rw [heq] at h
      exact (mul_eq_zero.mp h).resolve_left (div_ne_zero (by norm_num) hmass.ne')
    have hi : Set.EqOn e (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
      intro x hx
      by_contra hne
      have hp := integral_warp_mul_sq_pos K e hK.continuous he.continuous
        hpos hzero hone ⟨x, hx, hne⟩
      change 0 < probeMass K e at hp
      rw [hsq] at hp
      exact lt_irrefl _ hp
    have hc := hi.closure he.continuous continuous_const
    intro x hx
    have hz : e x = 0 := hc (by
      simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hx)
    exact sub_eq_zero.mp hz
  · intro hstat s hs
    rw [(rayleighQuotient_hasDerivAt K r s hK hr hs hzero hone hmass.ne').deriv]
    have hi : (∫ x in (0 : ℝ)..1, warp K x * s x *
        (meridionalJacobiOperator K r x - rayleighQuotient K r * r x)) = 0 := by
      calc
        _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
          dsimp only
          rw [hstat x hx', sub_self, mul_zero]
        _ = 0 := by simp
    rw [hi, mul_zero]

/-- At unit mass the Rayleigh eigenvalue is the complete action. -/
theorem rayleighQuotient_eq_of_probeMass_eq_one (K r : ℝ → ℝ)
    (hmass : probeMass K r = 1) : rayleighQuotient K r = meridionalAction K r := by
  simp only [rayleighQuotient, hmass, div_one]

/-- Unit-mass quotient stationarity has the complete action as its eigenvalue. -/
theorem rayleighQuotient_stationary_iff_of_probeMass_eq_one (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : probeMass K r = 1) :
    (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      deriv (fun t => rayleighQuotient K (fun x => r x + t * s x)) 0 = 0) ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        meridionalJacobiOperator K r x = meridionalAction K r * r x := by
  have hm : 0 < probeMass K r := by rw [hmass]; norm_num
  simpa only [rayleighQuotient_eq_of_probeMass_eq_one K r hmass] using
    rayleighQuotient_stationary_iff K r hK hr hpos hzero hone hm

/-- For zero action and positive mass, quotient stationarity is the zero-mode equation. -/
theorem rayleighQuotient_stationary_iff_of_action_eq_zero (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hmass : 0 < probeMass K r) (hAction : meridionalAction K r = 0) :
    (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      deriv (fun t => rayleighQuotient K (fun x => r x + t * s x)) 0 = 0) ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, meridionalJacobiOperator K r x = 0 := by
  have hValue : rayleighQuotient K r = 0 := by
    simp only [rayleighQuotient, hAction, zero_div]
  simpa only [hValue, zero_mul] using
    rayleighQuotient_stationary_iff K r hK hr hpos hzero hone hmass

/-- A local minimum along every smooth probe direction satisfies the full
Rayleigh eigen-equation. This is a necessary condition only. -/
theorem rayleighQuotient_euler_eq_of_isLocalMin (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : 0 < probeMass K r)
    (hmin : ∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      IsLocalMin (fun t => rayleighQuotient K (fun x => r x + t * s x)) 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      meridionalJacobiOperator K r x = rayleighQuotient K r * r x := by
  apply (rayleighQuotient_stationary_iff K r hK hr hpos hzero hone hmass).mp
  intro s hs
  have hd := rayleighQuotient_hasDerivAt K r s hK hr hs hzero hone hmass.ne'
  rw [hd.deriv]
  exact (hmin s hs).hasDerivAt_eq_zero hd

/-- The explicit normalization retains the original probe direction. -/
def normalizedProbe (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.sqrt (probeMass K r)) * r x

/-- The literal normalized probe has unit mass. -/
theorem probeMass_normalizedProbe (K r : ℝ → ℝ) (hmass : 0 < probeMass K r) :
    probeMass K (normalizedProbe K r) = 1 := by
  have heq : probeMass K (normalizedProbe K r) =
      (1 / Real.sqrt (probeMass K r)) ^ 2 * probeMass K r := by
    change (∫ x in (0 : ℝ)..1,
      warp K x * ((1 / Real.sqrt (probeMass K r)) * r x) ^ 2) =
        (1 / Real.sqrt (probeMass K r)) ^ 2 * (∫ x in (0 : ℝ)..1, warp K x * r x ^ 2)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [heq, div_pow, one_pow, Real.sq_sqrt hmass.le]
  field_simp [hmass.ne']

/-- The Rayleigh quotient is the actual action of the literal unit-mass normalization. -/
theorem meridionalAction_normalizedProbe (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : 0 < probeMass K r) :
    meridionalAction K (normalizedProbe K r) = rayleighQuotient K r := by
  change meridionalAction K (fun x => (1 / Real.sqrt (probeMass K r)) * r x) = _
  rw [meridionalAction_const_mul K r hK hr hzero hone,
    div_pow, one_pow, Real.sq_sqrt hmass.le]
  unfold rayleighQuotient
  ring

/-- The derivative of the actual action after literal unit-mass normalization
of a probe variation is the Rayleigh residual pairing. -/
theorem normalized_probe_action_hasDerivAt (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : 0 < probeMass K r) :
    HasDerivAt (fun t => meridionalAction K (normalizedProbe K (fun x => r x + t * s x)))
      (2 / probeMass K r * (∫ x in (0 : ℝ)..1, warp K x * s x *
        (meridionalJacobiOperator K r x - rayleighQuotient K r * r x))) 0 := by
  have hm := (probeMass_hasDerivAt K r s hK.continuous hr.continuous hs.continuous).continuousAt
  have hpos : ∀ᶠ t in nhds (0 : ℝ), 0 < probeMass K (fun x => r x + t * s x) :=
    hm.eventually (lt_mem_nhds (by simpa only [zero_mul, add_zero] using hmass))
  apply (rayleighQuotient_hasDerivAt K r s hK hr hs hzero hone hmass.ne').congr_of_eventuallyEq
  exact hpos.mono fun t ht => meridionalAction_normalizedProbe K (fun x => r x + t * s x)
    hK (hr.add (contDiff_const.mul hs)) hzero hone ht

/-- Local minima of the literal normalized-probe action satisfy the full
Rayleigh eigen-equation. Positive curvature and mass exclude vacuous normalization. -/
theorem normalized_probe_euler_eq_of_isLocalMin (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (hmass : 0 < probeMass K r)
    (hmin : ∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      IsLocalMin (fun t => meridionalAction K (normalizedProbe K (fun x => r x + t * s x))) 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      meridionalJacobiOperator K r x = rayleighQuotient K r * r x := by
  apply (rayleighQuotient_stationary_iff K r hK hr hpos hzero hone hmass).mp
  intro s hs
  rw [(rayleighQuotient_hasDerivAt K r s hK hr hs hzero hone hmass.ne').deriv]
  exact (hmin s hs).hasDerivAt_eq_zero
    (normalized_probe_action_hasDerivAt K r s hK hr hs hzero hone hmass)

end RicciFlowSharpEstimate.Geometry.AreaProfile
