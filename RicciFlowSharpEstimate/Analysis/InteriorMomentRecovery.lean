/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothBoxApproximation
import RicciFlowSharpEstimate.Analysis.InteriorMomentBasis
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth recovery of both moments inside a uniform box

An L2 function separated almost everywhere from both ends of a box admits
arbitrarily close globally smooth approximants inside the same box, with
both its zeroth and first interval moments preserved exactly.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem moment_norm_bound
    {f g φ : ℝ → ℝ} (hf : MemLp f 2 areaμ) (hg : MemLp g 2 areaμ)
    (hφ : AEStronglyMeasurable φ areaμ) (hb : ∀ᵐ x ∂areaμ, |φ x| ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : eLpNorm (f - g) 2 areaμ ≤ ENNReal.ofReal ε) :
    |∫ x, φ x * (f x - g x) ∂areaμ| ≤ ε := by
  let : IsProbabilityMeasure areaμ := ⟨by simp⟩
  have hm : AEStronglyMeasurable (fun x => φ x * (f x - g x)) areaμ :=
    hφ.mul (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
  have hmono : eLpNorm (fun x => φ x * (f x - g x)) 2 areaμ ≤
      eLpNorm (f - g) 2 areaμ := by
    apply eLpNorm_mono_ae hm
    filter_upwards [hb] with x hx
    simp only [Pi.sub_apply, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) hx
  have hnorm : ENNReal.ofReal ‖∫ x, φ x * (f x - g x) ∂areaμ‖ ≤ ENNReal.ofReal ε := by
    rw [ofReal_norm]
    calc
      _ ≤ ∫⁻ x, ‖φ x * (f x - g x)‖ₑ ∂areaμ :=
        enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => φ x * (f x - g x)) 1 areaμ :=
        (eLpNorm_one_eq_lintegral_enorm hm).symm
      _ ≤ eLpNorm (fun x => φ x * (f x - g x)) 2 areaμ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ ENNReal.ofReal ε := hmono.trans herr
  simpa only [Real.norm_eq_abs] using (ENNReal.ofReal_le_ofReal_iff hε).mp hnorm

private theorem unit_norm_bound {u : ℝ → ℝ} {D : ℝ}
    (hm : AEStronglyMeasurable u areaμ) (hb : ∀ᵐ x ∂areaμ, ‖u x‖ ≤ D) :
    eLpNorm u 2 areaμ ≤ ENNReal.ofReal D := by
  have hh := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hm hb
  simpa using hh

/-- A uniformly interior L2 function on the open unit interval admits
arbitrarily close globally smooth approximations in the original box,
with its zeroth and first interval moments preserved exactly. -/
theorem exists_contDiff_exact_moments_of_memLp_of_interior_box
    (f : ℝ → ℝ) (lo hi δ ε : ℝ) (hf : MemLp f 2 areaμ)
    (hδ : 0 < δ) (hbox : ∀ᵐ x ∂areaμ, f x ∈ Icc (lo + δ) (hi - δ))
    (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x, g x ∈ Icc lo hi) ∧
      (∫ x in (0 : ℝ)..1, g x) = (∫ x in (0 : ℝ)..1, f x) ∧
      (∫ x in (0 : ℝ)..1, x * g x) = (∫ x in (0 : ℝ)..1, x * f x) ∧
      eLpNorm (f - g) 2 areaμ ≤ ENNReal.ofReal ε := by
  let : IsProbabilityMeasure areaμ := ⟨by simp⟩
  have hab : lo + δ ≤ hi - δ := by
    obtain ⟨x, hx⟩ := hbox.exists
    exact hx.1.trans hx.2
  obtain ⟨ψ0, ψ1, B, hB, hψ0, hψ1, -, -, -, -, hbound,
    hm00, hm10, hm01, hm11⟩ := exists_contDiff_interior_moment_basis
  have hden : 0 < 2 * B + 1 := by linarith
  let τ : ℝ := min δ ε / (2 * B + 1)
  have hτ : 0 < τ := div_pos (lt_min hδ hε) hden
  have hτeq : τ * (2 * B + 1) = min δ ε := by
    dsimp only [τ]
    exact div_mul_cancel₀ _ hden.ne'
  have hτδ : τ + 2 * B * τ ≤ δ := by
    nlinarith [min_le_left δ ε]
  have hτε : τ + 2 * B * τ ≤ ε := by
    nlinarith [min_le_right δ ε]
  have hcorrectionNonneg : 0 ≤ 2 * B * τ := by positivity
  obtain ⟨v, hv, hvbox, herr⟩ :=
    exists_contDiff_approx_Icc_of_memLp f (lo + δ) (hi - δ) τ hab hf hbox hτ
  have hvLp : MemLp v 2 areaμ :=
    memLp_of_bounded (Eventually.of_forall hvbox) hv.continuous.aestronglyMeasurable 2
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
      (MemLp.integrable (by norm_num) hf)
  have hvi : IntervalIntegrable v volume 0 1 := hv.continuous.intervalIntegrable 0 1
  have hxmeas : AEStronglyMeasurable (fun x : ℝ => x) areaμ :=
    continuous_id.aestronglyMeasurable
  have hxbound : ∀ᵐ x ∂areaμ, |x| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_pos hx.1]
    exact hx.2.le
  have hwfi : IntervalIntegrable (fun x : ℝ => x * f x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
      (MemLp.integrable (by norm_num) (memLp_mul_of_ae_abs_le hxmeas hxbound hf))
  have hwvi : IntervalIntegrable (fun x : ℝ => x * v x) volume 0 1 :=
    (continuous_id.mul hv.continuous).intervalIntegrable 0 1
  let e0 : ℝ := (∫ x in (0 : ℝ)..1, f x) - (∫ x in (0 : ℝ)..1, v x)
  let e1 : ℝ := (∫ x in (0 : ℝ)..1, x * f x) - (∫ x in (0 : ℝ)..1, x * v x)
  have he0formula : e0 = ∫ x, (f x - v x) ∂areaμ := by
    dsimp only [e0]
    rw [← intervalIntegral.integral_sub hfi hvi,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have he1formula : e1 = ∫ x, x * (f x - v x) ∂areaμ := by
    dsimp only [e1]
    rw [← intervalIntegral.integral_sub hwfi hwvi,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have he0 : |e0| ≤ τ := by
    rw [he0formula]
    have hh := moment_norm_bound (φ := fun _ : ℝ => 1) hf hvLp
      aestronglyMeasurable_const (Eventually.of_forall fun _ => by norm_num) hτ.le herr
    simpa only [one_mul] using hh
  have he1 : |e1| ≤ τ := by
    rw [he1formula]
    exact moment_norm_bound hf hvLp hxmeas hxbound hτ.le herr
  let c : ℝ → ℝ := fun x => e0 * ψ0 x + e1 * ψ1 x
  have hc : ContDiff ℝ ∞ c :=
    ((contDiff_const (c := e0)).mul hψ0).add ((contDiff_const (c := e1)).mul hψ1)
  have hcabs (x : ℝ) : |c x| ≤ 2 * B * τ := by
    calc
      |c x| ≤ |e0 * ψ0 x| + |e1 * ψ1 x| := abs_add_le _ _
      _ = |e0| * |ψ0 x| + |e1| * |ψ1 x| := by rw [abs_mul, abs_mul]
      _ ≤ τ * B + τ * B :=
        add_le_add (mul_le_mul he0 (hbound x).1 (abs_nonneg _) hτ.le)
          (mul_le_mul he1 (hbound x).2 (abs_nonneg _) hτ.le)
      _ = 2 * B * τ := by ring
  have hcnorm : eLpNorm c 2 areaμ ≤ ENNReal.ofReal (2 * B * τ) := by
    apply unit_norm_bound hc.continuous.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hcabs x
  have hiψ0 : IntervalIntegrable ψ0 volume 0 1 := hψ0.continuous.intervalIntegrable 0 1
  have hiψ1 : IntervalIntegrable ψ1 volume 0 1 := hψ1.continuous.intervalIntegrable 0 1
  have hiwψ0 : IntervalIntegrable (fun x : ℝ => x * ψ0 x) volume 0 1 :=
    (continuous_id.mul hψ0.continuous).intervalIntegrable 0 1
  have hiwψ1 : IntervalIntegrable (fun x : ℝ => x * ψ1 x) volume 0 1 :=
    (continuous_id.mul hψ1.continuous).intervalIntegrable 0 1
  let g : ℝ → ℝ := fun x => v x + c x
  refine ⟨g, hv.add hc, ?_, ?_, ?_, ?_⟩
  · intro x
    have hvlo := (hvbox x).1
    have hvhi := (hvbox x).2
    obtain ⟨hclo, hchi⟩ := abs_le.mp (hcabs x)
    change lo ≤ v x + c x ∧ v x + c x ≤ hi
    constructor <;> linarith
  · dsimp only [g, c]
    rw [intervalIntegral.integral_add hvi ((hiψ0.const_mul e0).add (hiψ1.const_mul e1)),
      intervalIntegral.integral_add (hiψ0.const_mul e0) (hiψ1.const_mul e1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hm00, hm01]
    dsimp only [e0]
    ring
  · calc
      (∫ x in (0 : ℝ)..1, x * g x) =
          ∫ x in (0 : ℝ)..1, x * v x + (e0 * (x * ψ0 x) + e1 * (x * ψ1 x)) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [g, c]
        ring
      _ = (∫ x in (0 : ℝ)..1, x * v x) +
          (e0 * (∫ x in (0 : ℝ)..1, x * ψ0 x) +
            e1 * (∫ x in (0 : ℝ)..1, x * ψ1 x)) := by
        rw [intervalIntegral.integral_add hwvi
          ((hiwψ0.const_mul e0).add (hiwψ1.const_mul e1)),
          intervalIntegral.integral_add (hiwψ0.const_mul e0) (hiwψ1.const_mul e1),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..1, x * f x := by
        rw [hm10, hm11]
        dsimp only [e1]
        ring
  · have hdecomp : f - g = (f - v) - c := by
      funext x
      dsimp only [Pi.sub_apply, g]
      ring
    calc
      eLpNorm (f - g) 2 areaμ = eLpNorm ((f - v) - c) 2 areaμ := by rw [hdecomp]
      _ ≤ eLpNorm (f - v) 2 areaμ + eLpNorm c 2 areaμ :=
        eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal τ + ENNReal.ofReal (2 * B * τ) := add_le_add herr hcnorm
      _ = ENNReal.ofReal (τ + 2 * B * τ) :=
        (ENNReal.ofReal_add hτ.le hcorrectionNonneg).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hτε

end RicciFlowSharpEstimate.Analysis
