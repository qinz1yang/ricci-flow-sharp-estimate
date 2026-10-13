/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity
import RicciFlowSharpEstimate.Geometry.WeakProbeEulerFlux

/-!
# The actual local first-order system of the weak joint minimum

The canonical Euler momentum divided by the squared warp is the continuous
weak-operator representative. Genuine weak fundamental theorems and the actual
flux derivatives give locally absolutely continuous probe derivatives and
operator, with a coupled system on the physical interior. The curvature stays
measurable, the multiplier is the actual action, and no probe pole trace is added.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- For the continuous representatives of an actual recoverable minimum, the
first probe derivative is classical. Its next derivative and the canonical
operator/flux solve the displayed coupled system almost everywhere. The two
potentially nonsmooth coordinates are absolutely continuous on each compact
interior interval. Every field is the original probe, curvature or named flux. -/
theorem IsRecoverableAreaCompetitor.probe_first_order_system_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let P := weakProbeEulerFlux K r p z lam
    let q := fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2
    (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt r (p x) x) ∧
      ContDiffOn ℝ 1 r (Ioo (0 : ℝ) 1) ∧
      ContinuousOn q (Ioo (0 : ℝ) 1) ∧
      weakMeridionalOperator K r p z =ᵐ[areaμ] q ∧
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
        AbsolutelyContinuousOnInterval p a b ∧ AbsolutelyContinuousOnInterval q a b) ∧
      (∀ᵐ x ∂areaμ,
        HasDerivAt p ((q x - 2 * warpSlope K x * p x + K x * r x) / warp K x) x ∧
        HasDerivAt q ((P x - K x * warpSlope K x * warp K x * r x / 2) /
          warp K x ^ 2) x ∧
        HasDerivAt P (warp K x * K x * q x +
          K x * warpSlope K x * warp K x * p x / 2 -
          (K x ^ 2 * warp K x - K x * warpSlope K x ^ 2 / 2) * r x +
          lam * warp K x * r x) x) := by
  let lam := weakMeridionalAction K r p z
  let P := weakProbeEulerFlux K r p z lam
  let A := weakProbeEulerMomentum K r p z lam
  let q := fun x => A x / warp K x ^ 2
  have hg := h.geometry_bounds hC
  have hprimitive := h.primitive_local_regularity hC
  have hfD := hprimitive.1
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  obtain ⟨hUA, _hPAC, hAAC, _hP0, _hP1, _hA0, _hA1, hPD, hAD, hqc, hqeq⟩ :=
    h.probe_euler_flux_of_minimum hC hmin
  have hrD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt r (p x) x :=
    h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hx
  have hpD := h.2.1.weakDeriv_deriv.ae_hasDerivAt_of_continuousOn hp
  have hfC : ContDiffOn ℝ 1 (warp K) (Ioo (0 : ℝ) 1) :=
    (h.primitive_weak_derivatives hC).1.contDiffOn_one_of_continuousOn
      (hg.1.mono Ioo_subset_Icc_self) (hg.2.1.mono Ioo_subset_Icc_self)
  refine ⟨hrD, h.2.1.weakDeriv.contDiffOn_one_of_continuousOn hr hp, hqc, hqeq, ?_, ?_⟩
  · intro a ha b hb
    refine ⟨h.2.1.weakDeriv_deriv.absolutelyContinuousOnInterval hp ha hb, ?_⟩
    have hab : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
      intro x hx
      rcases mem_uIcc.mp hx with hx | hx
      · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
      · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩
    have hAab : AbsolutelyContinuousOnInterval A a b := by
      apply hAAC.mono
      simpa only [uIcc_of_le zero_le_one] using hab.trans Ioo_subset_Icc_self
    have hInv : ContDiffOn ℝ 1 (fun x => (warp K x ^ 2)⁻¹) (uIcc a b) :=
      ((hfC.pow 2).inv (fun x hx => pow_ne_zero 2 (hfpos x hx).ne')).mono hab
    simpa only [A, lam, Pi.mul_def, div_eq_mul_inv] using
      hAab.mul hInv.absolutelyContinuousOnInterval
  · filter_upwards [hpD, hUA, hPD, hAD, hqeq, ae_restrict_mem measurableSet_Ioo]
      with x hxP hxA hxPD hxAD hxq hxI
    have hfne : warp K x ≠ 0 := (hfpos x hxI).ne'
    have hzval : z x = (q x - 2 * warpSlope K x * p x + K x * r x) / warp K x := by
      apply (eq_div_iff hfne).mpr
      change weakMeridionalOperator K r p z x = q x at hxq
      dsimp only [weakMeridionalOperator] at hxq
      nlinarith only [hxq]
    refine ⟨hxP.congr_deriv hzval, ?_, ?_⟩
    · have hQ := hxAD.div ((hfD x hxI).pow 2) (pow_ne_zero 2 hfne)
      have hxA' : A x = warp K x ^ 2 * weakMeridionalOperator K r p z x := hxA.symm
      change HasDerivAt q _ x
      convert hQ using 1
      simp only [weakProbeFirstCoefficient, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      dsimp only [A, lam] at hxA'
      rw [hxA']
      field_simp [hfne]
      ring
    · change HasDerivAt P _ x
      convert hxPD using 1
      dsimp only [weakProbeZerothCoefficient]
      rw [hxq]
      ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
