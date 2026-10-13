/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfile
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete area action on the parabolic weak derivative graph

The probe, its first weak derivative, and its second weak derivative remain
separate entries. The curvature coefficients are the actual normalized
primitives. Primary coefficient bounds imply integrability of the complete
six-entry density, including both mixed and negative terms. Specializing the
jet entries to ordinary derivatives gives the existing action exactly.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual meridional expression evaluated on supplied weak jet entries.
Consumers tie these entries by `HasParabolicWeakDerivatives`. -/
def weakMeridionalOperator (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  warp K x * z x + 2 * warpSlope K x * p x - K x * r x

/-- The original complete density evaluated on supplied weak jet entries,
with the original interval and the actual curvature primitives. -/
def weakMeridionalAction (K r p z : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, meridionalActionDensity
    (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x)

/-- Ordinary derivatives recover the existing complete action by definition. -/
@[simp]
theorem weakMeridionalAction_deriv (K r : ℝ → ℝ) :
    weakMeridionalAction K r (deriv r) (deriv (deriv r)) = meridionalAction K r :=
  rfl

private theorem weakMeridionalActionDensity_eq (K r p z : ℝ → ℝ) (x : ℝ) :
    meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x) =
      warp K x * ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2) -
        K x * warpSlope K x * warp K x * r x * p x -
        (1 / 2 : ℝ) * (K x * (warpSlope K x) ^ 2 * (r x) ^ 2) := by
  unfold meridionalActionDensity weakMeridionalOperator
  ring

private theorem memLp_mul_of_ae_abs_coeff_le {μ : Measure ℝ}
    {a b v : ℝ → ℝ} {C : ℝ}
    (hav : AEStronglyMeasurable (fun x ↦ a x * v x) μ)
    (hbv : MemLp (fun x ↦ b x * v x) 2 μ)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ C * |b x|) :
    MemLp (fun x ↦ a x * v x) 2 μ := by
  apply hbv.of_le_mul (c := C) hav
  filter_upwards [hab] with x hx
  simpa only [Real.norm_eq_abs, abs_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (v x))

section WarpBounds

variable (K r p z : ℝ → ℝ) (hi : ℝ)
    (hgraph : Analysis.HasParabolicWeakDerivatives r p z)
    (hhi : 0 ≤ hi)
    (hK : AEStronglyMeasurable K areaμ)
    (hf : AEStronglyMeasurable (warp K) areaμ)
    (hb : AEStronglyMeasurable (warpSlope K) areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ hi)
    (hfbox : ∀ᵐ x ∂areaμ, 0 ≤ warp K x ∧ warp K x ≤ hi * (x * (1 - x)))
    (hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2)

include hgraph hhi hK hf hb hKbox hfbox hbbox

private theorem weakMeridionalAction_terms_integrable_of_warp_bounds :
    (MemLp (fun x => Real.sqrt (warp K x) * weakMeridionalOperator K r p z x) 2 areaμ ∧
      MemLp (fun x => (Real.sqrt (warp K x) * K x) * r x) 2 areaμ) ∧
    Integrable (fun x ↦ warp K x *
      ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2)) areaμ ∧
    Integrable (fun x ↦ K x * warpSlope K x * warp K x * r x * p x) areaμ ∧
    Integrable (fun x ↦ K x * (warpSlope K x) ^ 2 * (r x) ^ 2) areaμ := by
  let w : ℝ → ℝ := fun x ↦ x * (1 - x)
  let f : ℝ → ℝ := warp K
  let b : ℝ → ℝ := warpSlope K
  have hw : ∀ᵐ x ∂areaμ, 0 ≤ w x ∧ w x ≤ 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    refine ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), ?_⟩
    dsimp only [w]
    nlinarith only [hx.2, sq_nonneg x]
  have hp : AEStronglyMeasurable p areaμ :=
    hgraph.weakDeriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hz : AEStronglyMeasurable z areaμ :=
    hgraph.weakDeriv_deriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hsf : AEStronglyMeasurable (fun x ↦ Real.sqrt (f x)) areaμ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf
  have hsWeight : ∀ᵐ x ∂areaμ,
      Real.sqrt (f x) ≤ Real.sqrt hi * Real.sqrt (w x) := by
    filter_upwards [hfbox] with x hx
    calc
      Real.sqrt (f x) ≤ Real.sqrt (hi * w x) := Real.sqrt_le_sqrt hx.2
      _ = Real.sqrt hi * Real.sqrt (w x) := Real.sqrt_mul hhi (w x)
  have hsTop : ∀ᵐ x ∂areaμ, Real.sqrt (f x) ≤ Real.sqrt hi := by
    filter_upwards [hfbox, hw] with x hx hwx
    exact Real.sqrt_le_sqrt (hx.2.trans (mul_le_of_le_one_right hhi hwx.2))
  have hZ : MemLp (fun x ↦ (Real.sqrt (f x) * f x) * z x) 2 areaμ := by
    apply memLp_mul_of_ae_abs_coeff_le (C := hi * Real.sqrt hi)
      ((hsf.mul hf).mul hz) hgraph.memLp_weighted_secondDeriv
    filter_upwards [hfbox, hw, hsWeight] with x hx hwx hsx
    change |Real.sqrt (f x) * f x| ≤ hi * Real.sqrt hi * |w x * Real.sqrt (w x)|
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx.1),
      abs_of_nonneg (mul_nonneg hwx.1 (Real.sqrt_nonneg _))]
    calc
      Real.sqrt (f x) * f x ≤
          (Real.sqrt hi * Real.sqrt (w x)) * (hi * w x) :=
        mul_le_mul hsx hx.2 hx.1 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (hi * Real.sqrt hi) * (w x * Real.sqrt (w x)) := by ring
  have hP : MemLp (fun x ↦ (Real.sqrt (f x) * b x) * p x) 2 areaμ := by
    apply memLp_mul_of_ae_abs_coeff_le (C := 2 * Real.sqrt hi)
      ((hsf.mul hb).mul hp) hgraph.memLp_weighted_deriv
    filter_upwards [hbbox, hsWeight] with x hx hsx
    change |Real.sqrt (f x) * b x| ≤ 2 * Real.sqrt hi * |Real.sqrt (w x)|
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt (f x) * |b x| ≤ (Real.sqrt hi * Real.sqrt (w x)) * 2 :=
        mul_le_mul hsx hx (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (2 * Real.sqrt hi) * Real.sqrt (w x) := by ring
  have hR : MemLp (fun x ↦ (Real.sqrt (f x) * K x) * r x) 2 areaμ := by
    apply memLp_mul_of_ae_abs_coeff_le (b := fun _ ↦ 1) (C := Real.sqrt hi * hi)
      ((hsf.mul hK).mul hgraph.memLp.aestronglyMeasurable)
      (by simpa only [one_mul] using hgraph.memLp)
    filter_upwards [hKbox, hsTop] with x hx hsx
    change |Real.sqrt (f x) * K x| ≤ Real.sqrt hi * hi * |(1 : ℝ)|
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hx.1, abs_one, mul_one]
    exact mul_le_mul hsx hx.2 hx.1 (Real.sqrt_nonneg hi)
  have hQ : MemLp (fun x ↦ Real.sqrt (f x) * weakMeridionalOperator K r p z x)
      2 areaμ := by
    apply ((hZ.add (hP.const_mul 2)).sub hR).ae_eq
    filter_upwards [] with x
    change (Real.sqrt (f x) * f x) * z x +
        2 * ((Real.sqrt (f x) * b x) * p x) - (Real.sqrt (f x) * K x) * r x =
      Real.sqrt (f x) * (f x * z x + 2 * b x * p x - K x * r x)
    ring
  have hQsq : Integrable (fun x ↦ f x * (weakMeridionalOperator K r p z x) ^ 2)
      areaμ := by
    apply hQ.integrable_sq.congr
    filter_upwards [hfbox] with x hx
    rw [mul_pow, Real.sq_sqrt hx.1]
  have hRsq : Integrable (fun x ↦ f x * (K x * r x) ^ 2) areaμ := by
    apply hR.integrable_sq.congr
    filter_upwards [hfbox] with x hx
    calc
      ((Real.sqrt (f x) * K x) * r x) ^ 2 =
          (Real.sqrt (f x)) ^ 2 * (K x * r x) ^ 2 := by ring
      _ = f x * (K x * r x) ^ 2 := by rw [Real.sq_sqrt hx.1]
  have hPositive : Integrable (fun x ↦ f x *
      ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2)) areaμ := by
    apply (hQsq.add hRsq).congr
    filter_upwards [] with x
    simp only [Pi.add_apply, mul_add]
  have hMixed : Integrable (fun x ↦ K x * b x * f x * r x * p x) areaμ := by
    apply (hR.integrable_mul hP).congr
    filter_upwards [hfbox] with x hx
    change ((Real.sqrt (f x) * K x) * r x) * ((Real.sqrt (f x) * b x) * p x) = _
    calc
      _ = (Real.sqrt (f x)) ^ 2 * (K x * b x * r x * p x) := by ring
      _ = K x * b x * f x * r x * p x := by rw [Real.sq_sqrt hx.1]; ring
  have hPotential : Integrable (fun x ↦ K x * (b x) ^ 2 * (r x) ^ 2) areaμ := by
    apply hgraph.integrable_sq.bdd_mul (c := hi * 4) (hK.mul (hb.pow 2))
    filter_upwards [hKbox, hbbox] with x hx hbx
    have hbsq : (b x) ^ 2 ≤ 4 := by
      have hh := (sq_le_sq₀ (abs_nonneg (b x)) (show (0 : ℝ) ≤ 2 by norm_num)).mpr hbx
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
    change ‖K x * b x ^ 2‖ ≤ hi * 4
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul hx.2 hbsq (sq_nonneg _) hhi
  exact ⟨⟨hQ, hR⟩, hPositive, hMixed, hPotential⟩

/-- The graph and actual coefficient bounds put both positive-square
factors of the complete action in L², including the curvature/probe product. -/
theorem memLp_weak_operator_and_potential_of_warp_bounds :
    MemLp (fun x => Real.sqrt (warp K x) * weakMeridionalOperator K r p z x) 2 areaμ ∧
      MemLp (fun x => Real.sqrt (warp K x) * (K x * r x)) 2 areaμ := by
  have h := (weakMeridionalAction_terms_integrable_of_warp_bounds
    K r p z hi hgraph hhi hK hf hb hKbox hfbox hbbox).1
  simpa only [mul_assoc] using h

/-- Primary a.e. bounds on the actual curvature primitives and membership in
the weak derivative graph imply integrability of the literal complete density. -/
theorem integrable_weakMeridionalActionDensity_of_warp_bounds :
    Integrable (fun x ↦ meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (p x) (z x)) areaμ := by
  obtain ⟨_, hpos, hmix, hpot⟩ := weakMeridionalAction_terms_integrable_of_warp_bounds
    K r p z hi hgraph hhi hK hf hb hKbox hfbox hbbox
  apply ((hpos.sub hmix).sub (hpot.const_mul (1 / 2 : ℝ))).congr
  exact Eventually.of_forall fun x ↦ (weakMeridionalActionDensity_eq K r p z x).symm

/-- The same primary bounds make the original interval action integrable. -/
theorem weakMeridionalAction_intervalIntegrable_of_warp_bounds :
    IntervalIntegrable (fun x ↦ meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (p x) (z x)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  exact integrable_weakMeridionalActionDensity_of_warp_bounds
    K r p z hi hgraph hhi hK hf hb hKbox hfbox hbbox

/-- The complete weak action separates into its two positive square terms,
its mixed term, and its negative potential term, all genuinely integrable. -/
theorem weakMeridionalAction_decomposition_of_warp_bounds :
    weakMeridionalAction K r p z =
      (∫ x, warp K x * ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2) ∂areaμ) -
      (∫ x, K x * warpSlope K x * warp K x * r x * p x ∂areaμ) -
      (1 / 2 : ℝ) * (∫ x, K x * (warpSlope K x) ^ 2 * (r x) ^ 2 ∂areaμ) := by
  obtain ⟨_, hpos, hmix, hpot⟩ := weakMeridionalAction_terms_integrable_of_warp_bounds
    K r p z hi hgraph hhi hK hf hb hKbox hfbox hbbox
  rw [weakMeridionalAction, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ x, (warp K x * ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2) -
        K x * warpSlope K x * warp K x * r x * p x) -
        (1 / 2 : ℝ) * (K x * (warpSlope K x) ^ 2 * (r x) ^ 2) ∂areaμ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ weakMeridionalActionDensity_eq K r p z x)
    _ = _ := by
      have hminus : Integrable (fun x =>
          warp K x * ((weakMeridionalOperator K r p z x) ^ 2 + (K x * r x) ^ 2) -
            K x * warpSlope K x * warp K x * r x * p x) areaμ := hpos.sub hmix
      rw [integral_sub hminus (hpot.const_mul (1 / 2 : ℝ)),
        integral_sub hpos hmix, integral_const_mul]

end WarpBounds

end RicciFlowSharpEstimate.Geometry.AreaProfile
