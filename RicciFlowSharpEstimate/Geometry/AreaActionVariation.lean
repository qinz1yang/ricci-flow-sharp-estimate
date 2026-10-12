/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionFactorization

/-!
# Full fixed-geometry variation and the smooth zero-mode equation

The actual operator is symmetric with weight given by the original area warp.
Its Green flux vanishes at the physical poles for all smooth probes. The complete
quadratic variation yields a fourth-order equation, including its endpoint values,
without imposing Dirichlet or Neumann conditions or asserting a nonzero solution.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The actual second-order operator has a Green flux that vanishes at a zero warp. -/
def meridionalGreenFlux (K r s : ℝ → ℝ) (x : ℝ) : ℝ :=
  warp K x ^ 2 * (deriv r x * s x - r x * deriv s x)

theorem meridionalGreenFlux_hasDerivAt (K r s : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) (x : ℝ) :
    HasDerivAt (meridionalGreenFlux K r s)
      (warp K x * meridionalOperator K r x * s x -
        warp K x * r x * meridionalOperator K s x) x := by
  have hr1 := (contDiff_infty_iff_deriv.mp hr).2
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hdr := (hr.differentiable (by simp) x).hasDerivAt
  have hds := (hs.differentiable (by simp) x).hasDerivAt
  have hdr1 := (hr1.differentiable (by simp) x).hasDerivAt
  have hds1 := (hs1.differentiable (by simp) x).hasDerivAt
  convert ((warp_hasDerivAt K hK x).pow 2).mul
    ((hdr1.mul hds).sub (hdr.mul hds1)) using 1
  · rfl
  · simp only [meridionalOperator, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    ring

theorem meridionalGreenFlux_endpoints (K r s : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    meridionalGreenFlux K r s 0 = 0 ∧ meridionalGreenFlux K r s 1 = 0 := by
  simp [meridionalGreenFlux, warp_one K hK hzero hone]

/-- Green symmetry with no Dirichlet or Neumann conditions on the smooth probes. -/
theorem integral_warp_mul_operator_mul (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, warp K x * meridionalOperator K r x * s x) =
      ∫ x in (0 : ℝ)..1, warp K x * r x * meridionalOperator K s x := by
  have hf := (warp_contDiff K hK).continuous
  have hLr := (meridionalOperator_contDiff K r hK hr).continuous
  have hLs := (meridionalOperator_contDiff K s hK hs).continuous
  have hleft : Continuous (fun x => warp K x * meridionalOperator K r x * s x) :=
    (hf.mul hLr).mul hs.continuous
  have hright : Continuous (fun x => warp K x * r x * meridionalOperator K s x) :=
    (hf.mul hr.continuous).mul hLs
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => meridionalGreenFlux_hasDerivAt K r s hK.continuous hr hs x)
    ((hleft.sub hright).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (hleft.intervalIntegrable 0 1)
    (hright.intervalIntegrable 0 1)] at hi
  obtain ⟨h0, h1⟩ := meridionalGreenFlux_endpoints K r s hK.continuous hzero hone
  rw [h0, h1] at hi
  linarith

/-- The fourth-order operator in the full fixed-geometry Euler equation. -/
def meridionalJacobiOperator (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  meridionalOperator K (meridionalOperator K r) x +
    warpSlope K x * deriv K x / 2 * r x

/-- The Euler expression uses the actual derivatives of the same smooth probe. -/
theorem meridionalJacobiOperator_contDiff (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (meridionalJacobiOperator K r) := by
  have hL := meridionalOperator_contDiff K r hK hr
  have hLL := meridionalOperator_contDiff K (meridionalOperator K r) hK hL
  have hf1 := warpSlope_contDiff K hK
  have hK1 := (contDiff_infty_iff_deriv.mp hK).2
  unfold meridionalJacobiOperator
  fun_prop

/-- The square-potential polarization is the pairing with the actual Euler operator. -/
theorem integral_meridionalOperator_pair_eq_jacobi (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, warp K x * meridionalOperator K r x *
      meridionalOperator K s x +
        (warp K x * warpSlope K x * deriv K x / 2) * r x * s x) =
      ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x := by
  have hf := (warp_contDiff K hK).continuous
  have hf1 := (warpSlope_contDiff K hK).continuous
  have hK1 := hK.continuous_deriv (by simp)
  have hLr := meridionalOperator_contDiff K r hK hr
  have hLs := meridionalOperator_contDiff K s hK hs
  have hLL := (meridionalOperator_contDiff K (meridionalOperator K r) hK hLr).continuous
  have hleft : Continuous (fun x => warp K x * meridionalOperator K r x *
      meridionalOperator K s x) := by fun_prop
  have hright : Continuous (fun x => warp K x * meridionalOperator K
      (meridionalOperator K r) x * s x) := by fun_prop
  have hpot : Continuous (fun x =>
      (warp K x * warpSlope K x * deriv K x / 2) * r x * s x) := by fun_prop
  have hgreen := integral_warp_mul_operator_mul K (meridionalOperator K r) s
    hK hLr hs hzero hone
  rw [intervalIntegral.integral_add (hleft.intervalIntegrable 0 1)
    (hpot.intervalIntegrable 0 1), ← hgreen,
    ← intervalIntegral.integral_add (hright.intervalIntegrable 0 1)
      (hpot.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro x _
  unfold meridionalJacobiOperator
  ring

/-- An affine smooth-probe variation is taken through its actual first and second derivatives. -/
theorem meridionalOperator_add_mul (K r s : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) (t x : ℝ) :
    meridionalOperator K (fun y => r y + t * s y) x =
      meridionalOperator K r x + t * meridionalOperator K s x := by
  have hr1 := (contDiff_infty_iff_deriv.mp hr).2
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hd : deriv (fun y => r y + t * s y) = fun y => deriv r y + t * deriv s y := by
    funext y
    exact ((hr.differentiable (by simp) y).hasDerivAt.add
      ((hs.differentiable (by simp) y).hasDerivAt.const_mul t)).deriv
  have hdd : deriv (deriv (fun y => r y + t * s y)) =
      fun y => deriv (deriv r) y + t * deriv (deriv s) y := by
    rw [hd]
    funext y
    exact ((hr1.differentiable (by simp) y).hasDerivAt.add
      ((hs1.differentiable (by simp) y).hasDerivAt.const_mul t)).deriv
  unfold meridionalOperator
  rw [hdd, hd]
  ring

/-- Exact complete-action variation, including the full quadratic remainder. -/
theorem meridionalAction_add_mul (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (t : ℝ) :
    meridionalAction K (fun x => r x + t * s x) = meridionalAction K r +
      2 * t * (∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) +
      t ^ 2 * meridionalAction K s := by
  have hf := (warp_contDiff K hK).continuous
  have hf1 := (warpSlope_contDiff K hK).continuous
  have hK1 := hK.continuous_deriv (by simp)
  have hLr := (meridionalOperator_contDiff K r hK hr).continuous
  have hLs := (meridionalOperator_contDiff K s hK hs).continuous
  let F := fun x => warp K x * meridionalOperator K r x ^ 2 +
    (warp K x * warpSlope K x * deriv K x / 2) * r x ^ 2
  let G := fun x => warp K x * meridionalOperator K r x * meridionalOperator K s x +
    (warp K x * warpSlope K x * deriv K x / 2) * r x * s x
  let T := fun x => warp K x * meridionalOperator K s x ^ 2 +
    (warp K x * warpSlope K x * deriv K x / 2) * s x ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hT : Continuous T := by dsimp [T]; fun_prop
  rw [meridionalAction_eq_square_potential K _ hK
    (hr.add (contDiff_const.mul hs)) hzero hone]
  calc
    _ = ∫ x in (0 : ℝ)..1, F x + (2 * t) * G x + t ^ 2 * T x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [meridionalOperator_add_mul K r s hr hs]
      dsimp [F, G, T]
      ring
    _ = (∫ x in (0 : ℝ)..1, F x) + 2 * t * (∫ x in (0 : ℝ)..1, G x) +
        t ^ 2 * (∫ x in (0 : ℝ)..1, T x) := by
      rw [intervalIntegral.integral_add
        ((hF.intervalIntegrable 0 1).add ((hG.intervalIntegrable 0 1).const_mul (2 * t)))
        ((hT.intervalIntegrable 0 1).const_mul (t ^ 2)),
        intervalIntegral.integral_add (hF.intervalIntegrable 0 1)
          ((hG.intervalIntegrable 0 1).const_mul (2 * t))]
      simp only [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [show (∫ x in (0 : ℝ)..1, F x) = meridionalAction K r from
        (meridionalAction_eq_square_potential K r hK hr hzero hone).symm,
        show (∫ x in (0 : ℝ)..1, T x) = meridionalAction K s from
        (meridionalAction_eq_square_potential K s hK hs hzero hone).symm]
      rw [show (∫ x in (0 : ℝ)..1, G x) =
          ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x from
        integral_meridionalOperator_pair_eq_jacobi K r s hK hr hs hzero hone]

/-- The actual parameter derivative at zero is the full Euler pairing. -/
theorem meridionalAction_hasDerivAt (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    HasDerivAt (fun t => meridionalAction K (fun x => r x + t * s x))
      (2 * ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) 0 := by
  have heq : (fun t => meridionalAction K (fun x => r x + t * s x)) =
      fun t => meridionalAction K r +
        2 * t * (∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) +
        t ^ 2 * meridionalAction K s := by
    funext t
    exact meridionalAction_add_mul K r s hK hr hs hzero hone t
  rw [heq]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
    (∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x)).const_add
    (meridionalAction K r) |>.add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (meridionalAction K s)) using 1
  · funext t
    rfl
  · norm_num

/-- The natural weighted probe mass is positive for every probe nonzero in the physical interior. -/
theorem integral_warp_mul_sq_pos (K r : ℝ → ℝ) (hK : Continuous K) (hr : Continuous r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hne : ∃ x ∈ Set.Ioo (0 : ℝ) 1, r x ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2 := by
  apply intervalIntegral.integral_pos (by norm_num)
    (((warp_continuous K hK).mul (hr.pow 2)).continuousOn)
  · intro x hx
    rcases lt_or_eq_of_le hx.2 with hx1 | rfl
    · exact mul_nonneg (warp_pos_of_moments K hK hpos hzero hone x ⟨hx.1, hx1⟩).le
        (sq_nonneg _)
    · change 0 ≤ warp K 1 * r 1 ^ 2
      simp only [warp_one K hK hzero hone, zero_mul, le_refl]
  · obtain ⟨x, hx, hne⟩ := hne
    exact ⟨x, ⟨hx.1.le, hx.2.le⟩,
      mul_pos (warp_pos_of_moments K hK hpos hzero hone x hx) (sq_pos_of_ne_zero hne)⟩

/-- Smooth stationarity of the complete action is exactly the fourth-order equation,
including its continuous endpoint values. This does not assert a nonzero solution exists. -/
theorem meridionalAction_stationary_iff (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
      deriv (fun t => meridionalAction K (fun x => r x + t * s x)) 0 = 0) ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, meridionalJacobiOperator K r x = 0 := by
  have hJ := meridionalJacobiOperator_contDiff K r hK hr
  constructor
  · intro hstat
    have h := hstat (meridionalJacobiOperator K r) hJ
    rw [(meridionalAction_hasDerivAt K r (meridionalJacobiOperator K r)
      hK hr hJ hzero hone).deriv] at h
    have hsq : (∫ x in (0 : ℝ)..1, warp K x * meridionalJacobiOperator K r x ^ 2) = 0 := by
      have heq : (∫ x in (0 : ℝ)..1, warp K x * meridionalJacobiOperator K r x *
          meridionalJacobiOperator K r x) =
          ∫ x in (0 : ℝ)..1, warp K x * meridionalJacobiOperator K r x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      rw [heq] at h
      linarith
    have hi : Set.EqOn (meridionalJacobiOperator K r) (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
      intro x hx
      by_contra hne
      have hp := integral_warp_mul_sq_pos K (meridionalJacobiOperator K r)
        hK.continuous hJ.continuous hpos hzero hone ⟨x, hx, hne⟩
      rw [hsq] at hp
      exact lt_irrefl _ hp
    have hc := hi.closure hJ.continuous continuous_const
    intro x hx
    apply hc
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hx
  · intro hstat s hs
    rw [(meridionalAction_hasDerivAt K r s hK hr hs hzero hone).deriv]
    have hi : (∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) = 0 := by
      calc
        _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
          dsimp only
          rw [hstat x hx', mul_zero]
        _ = 0 := by simp
    rw [hi, mul_zero]

/-- The south-pole value forced by the regular fourth-order equation. -/
theorem meridionalJacobiOperator_zero (K r : ℝ → ℝ) :
    meridionalJacobiOperator K r 0 =
      4 * deriv (meridionalOperator K r) 0 - K 0 * meridionalOperator K r 0 +
        deriv K 0 * r 0 := by
  simp only [meridionalJacobiOperator, meridionalOperator, warp_zero, warpSlope_zero]
  ring

/-- The north-pole value forced by the regular fourth-order equation. -/
theorem meridionalJacobiOperator_one (K r : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    meridionalJacobiOperator K r 1 =
      -4 * deriv (meridionalOperator K r) 1 - K 1 * meridionalOperator K r 1 -
        deriv K 1 * r 1 := by
  simp only [meridionalJacobiOperator, meridionalOperator,
    warp_one K hK hzero hone, warpSlope_one K hzero]
  ring

/-- The full action is the weighted pairing of the probe with its Euler operator. -/
theorem meridionalAction_eq_integral_jacobi (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    meridionalAction K r =
      ∫ x in (0 : ℝ)..1, warp K x * r x * meridionalJacobiOperator K r x := by
  rw [meridionalAction_eq_square_potential K r hK hr hzero hone,
    ← integral_meridionalOperator_pair_eq_jacobi K r r hK hr hr hzero hone]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- Scaling the same actual probe scales its complete action quadratically. -/
theorem meridionalAction_const_mul (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (c : ℝ) :
    meridionalAction K (fun x => c * r x) = c ^ 2 * meridionalAction K r := by
  have h := meridionalAction_add_mul K (fun _ => 0) r hK contDiff_const hr hzero hone c
  have hL0 : meridionalOperator K (fun _ => 0) = fun _ => 0 := by
    funext x
    simp [meridionalOperator]
  have hJ0 : meridionalJacobiOperator K (fun _ => 0) = fun _ => 0 := by
    funext x
    simp [meridionalJacobiOperator, hL0]
  have hA0 : meridionalAction K (fun _ => 0) = 0 := by
    simp [meridionalAction, meridionalActionDensity]
  simpa only [zero_add, hA0, hJ0, mul_zero, intervalIntegral.integral_zero, add_zero] using h

/-- A probe nonzero on the physical interior admits positive weighted normalization
without changing its direction or replacing either of its derivatives. -/
theorem exists_normalized_area_probe (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hne : ∃ x ∈ Set.Ioo (0 : ℝ) 1, r x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      (∫ x in (0 : ℝ)..1, warp K x * (c * r x) ^ 2) = 1 ∧
      meridionalAction K (fun x => c * r x) = c ^ 2 * meridionalAction K r := by
  let m := ∫ x in (0 : ℝ)..1, warp K x * r x ^ 2
  have hm : 0 < m := integral_warp_mul_sq_pos K r hK.continuous hr.continuous
    hpos hzero hone hne
  refine ⟨1 / Real.sqrt m, one_div_pos.mpr (Real.sqrt_pos.mpr hm), ?_,
    meridionalAction_const_mul K r hK hr hzero hone _⟩
  calc
    _ = (1 / Real.sqrt m) ^ 2 * m := by
      calc
        _ = ∫ x in (0 : ℝ)..1, (1 / Real.sqrt m) ^ 2 * (warp K x * r x ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
        _ = _ := intervalIntegral.integral_const_mul _ _
    _ = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt hm.le]
      field_simp [hm.ne']

end RicciFlowSharpEstimate.Geometry.AreaProfile
