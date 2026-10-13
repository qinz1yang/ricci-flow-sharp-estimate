/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.L2UniformIntegrability
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Products with an almost-everywhere convergent bounded L2 sequence

On a finite measure space, a uniformly L2-bounded sequence that converges
almost everywhere has convergent integral pairings against every L2 test.
More strongly, its product with a strongly L2-convergent sequence converges
in the literal L1 integral. The proof obtains native uniform integrability
from restricted Hölder estimates and uses Vitali convergence.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem eLpNorm_mul_one_le (u v : α → ℝ) :
    eLpNorm (u * v) 1 μ ≤ eLpNorm u 2 μ * eLpNorm v 2 μ := by
  change eLpNorm (u • v) 1 μ ≤ _
  exact eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) zero_lt_one

private theorem eLpNorm_two_le_sqrt_integral_bound
    {u : α → ℝ} (hu : MemLp u 2 μ) {M : ℝ}
    (hM : (∫ a, u a ^ 2 ∂μ) ≤ M) :
    eLpNorm u 2 μ ≤ ENNReal.ofReal (Real.sqrt M) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hu]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    ← one_div, ← Real.sqrt_eq_rpow] using
    (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hM))

/-- Multiplying a uniformly L2-bounded family by one fixed L2 function gives
a natively uniformly integrable L1 family. No finiteness of the measure is
needed for this uniform-integrability statement. -/
theorem uniformIntegrable_mul_left_of_eLpNorm_two_bound
    {ι : Type*} {f : ι → α → ℝ} {v : α → ℝ} (hv : MemLp v 2 μ)
    (C : NNReal) (hC : ∀ i, eLpNorm (f i) 2 μ ≤ C) :
    UniformIntegrable (fun i ↦ v * f i) 1 μ := by
  have hsmall := hv.tendsto_eLpNorm_restrict_zero (by norm_num) (by simp)
  have hmajorRaw := ENNReal.Tendsto.mul_const (b := (C : ℝ≥0∞)) hsmall
    (Or.inr ENNReal.coe_ne_top)
  have hmajor : Tendsto
      (fun ε ↦ (⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm v 2 (μ.restrict s)) * C)
      (nhds 0) (nhds 0) := by
    simpa only [zero_mul] using hmajorRaw
  have hUI : UnifIntegrable (fun i ↦ v * f i) 1 μ := by
    change Tendsto _ (nhds 0) (nhds 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ ↦ zero_le) ?_
    intro ε
    refine iSup_le fun i ↦ iSup_le fun s ↦ iSup_le fun hs ↦ ?_
    calc
      eLpNorm (v * f i) 1 (μ.restrict s) ≤
          eLpNorm v 2 (μ.restrict s) * eLpNorm (f i) 2 (μ.restrict s) :=
        eLpNorm_mul_one_le v (f i)
      _ ≤ (⨆ (t : Set α) (_ : μ t ≤ ε), eLpNorm v 2 (μ.restrict t)) * C :=
        mul_le_mul'
          (le_iSup_of_le s (le_iSup_of_le hs le_rfl))
          ((eLpNorm_restrict_le (f i) 2 μ s).trans (hC i))
  refine ⟨hUI, (eLpNorm v 2 μ).toNNReal * C, fun i ↦ ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hv.eLpNorm_ne_top]
  exact (eLpNorm_mul_one_le v (f i)).trans (mul_le_mul' le_rfl (hC i))

/-- A fixed L2 test times an almost-everywhere convergent sequence with
uniformly bounded square integrals converges strongly in L1. -/
theorem tendsto_eLpNorm_one_mul_sub_of_ae_tendsto_of_integral_sq_bound
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g v : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hv : MemLp v 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ a, f n a ^ 2 ∂μ) ≤ M)
    (hfg : ∀ᵐ a ∂μ, Tendsto (fun n ↦ f n a) atTop (nhds (g a))) :
    Tendsto (fun n ↦ eLpNorm (v * f n - v * g) 1 μ) atTop (nhds 0) := by
  have hg : MemLp g 2 μ :=
    memLp_two_of_ae_tendsto_of_integral_sq_bound f g hf M hM hfg
  let C : NNReal := ⟨Real.sqrt M, Real.sqrt_nonneg M⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt M) :=
    (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg M)).symm
  have hbound (n : ℕ) : eLpNorm (f n) 2 μ ≤ C := by
    rw [hC]
    exact eLpNorm_two_le_sqrt_integral_bound (hf n) (hM n)
  have hUI := uniformIntegrable_mul_left_of_eLpNorm_two_bound hv C hbound
  refine tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
    (fun n ↦ hv.aestronglyMeasurable.mul (hf n).aestronglyMeasurable)
    (hv.mul hg) hUI.unifIntegrable ?_
  filter_upwards [hfg] with a ha
  exact tendsto_const_nhds.mul ha

/-- If the first factor converges strongly in L2 and the second converges
almost everywhere with uniformly bounded square integrals, their literal
products converge strongly in L1. The L2 membership of the second limit is
deduced from the square-integral bound. -/
theorem tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hu : ∀ n, MemLp (u n) 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ a, u n a ^ 2 ∂μ) ≤ M)
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) 2 μ) atTop (nhds 0))
    (huv : ∀ᵐ a ∂μ, Tendsto (fun n ↦ u n a) atTop (nhds (v a))) :
    Tendsto (fun n ↦ ∫ a, |f n a * u n a - g a * v a| ∂μ)
      atTop (nhds 0) := by
  have hv : MemLp v 2 μ :=
    memLp_two_of_ae_tendsto_of_integral_sq_bound u v hu M hM huv
  have hfixed := tendsto_eLpNorm_one_mul_sub_of_ae_tendsto_of_integral_sq_bound
    hu hg M hM huv
  have hmajorRaw := ENNReal.Tendsto.mul_const hfg
    (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt M)))
  have hmajor : Tendsto
      (fun n ↦ eLpNorm (f n - g) 2 μ * ENNReal.ofReal (Real.sqrt M))
      atTop (nhds 0) := by
    simpa only [zero_mul] using hmajorRaw
  have herror : Tendsto (fun n ↦ eLpNorm ((f n - g) * u n) 1 μ)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ ↦ zero_le) ?_
    intro n
    exact (eLpNorm_mul_one_le (f n - g) (u n)).trans
      (mul_le_mul' le_rfl (eLpNorm_two_le_sqrt_integral_bound (hu n) (hM n)))
  have hsumRaw := herror.add hfixed
  have hsum : Tendsto
      (fun n ↦ eLpNorm ((f n - g) * u n) 1 μ + eLpNorm (g * u n - g * v) 1 μ)
      atTop (nhds 0) := by
    simpa only [zero_add] using hsumRaw
  have hfull : Tendsto (fun n ↦ eLpNorm (f n * u n - g * v) 1 μ)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) ?_
    intro n
    have heq : f n * u n - g * v = (f n - g) * u n + (g * u n - g * v) := by
      ext a
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
      ring
    change eLpNorm (f n * u n - g * v) 1 μ ≤
      eLpNorm ((f n - g) * u n) 1 μ + eLpNorm (g * u n - g * v) 1 μ
    rw [heq]
    exact eLpNorm_add_le le_rfl
  have hmeas (n : ℕ) : AEStronglyMeasurable (f n * u n - g * v) μ :=
    ((hf n).aestronglyMeasurable.mul (hu n).aestronglyMeasurable).sub
      (hg.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  have hid (n : ℕ) : (eLpNorm (f n * u n - g * v) 1 μ).toReal =
      ∫ a, |f n a * u n a - g a * v a| ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hmeas n)]
    symm
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply] using
      (integral_norm_eq_lintegral_enorm (hmeas n))
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hfull
  simpa only [Function.comp_def, ENNReal.toReal_zero, hid] using hreal

/-- On a finite measure space, a uniform square-integral bound upgrades
almost-everywhere convergence to convergence of the literal L1 distance. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto_of_integral_sq_bound
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ a, f n a ^ 2 ∂μ) ≤ M)
    (hfg : ∀ᵐ a ∂μ, Tendsto (fun n ↦ f n a) atTop (nhds (g a))) :
    Tendsto (fun n ↦ ∫ a, |f n a - g a| ∂μ) atTop (nhds 0) := by
  have hconst : MemLp (fun _ : α ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hzero : Tendsto
      (fun _ : ℕ ↦ eLpNorm ((fun _ : α ↦ (1 : ℝ)) - (fun _ : α ↦ (1 : ℝ))) 2 μ)
      atTop (nhds 0) := by
    simpa only [sub_self, eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0))
  simpa only [one_mul] using
    (tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (fun _ ↦ hconst) hconst hf M hM hzero hfg)

/-- Every L2 test detects the weak L2 limit of an almost-everywhere
convergent sequence with uniformly bounded square integrals. -/
theorem tendsto_integral_mul_of_ae_tendsto_of_integral_sq_bound
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g v : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hv : MemLp v 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ a, f n a ^ 2 ∂μ) ≤ M)
    (hfg : ∀ᵐ a ∂μ, Tendsto (fun n ↦ f n a) atTop (nhds (g a))) :
    Tendsto (fun n ↦ ∫ a, f n a * v a ∂μ) atTop
      (nhds (∫ a, g a * v a ∂μ)) := by
  have hLp := tendsto_eLpNorm_one_mul_sub_of_ae_tendsto_of_integral_sq_bound
    hf hv M hM hfg
  have hi (n : ℕ) : Integrable (v * f n) μ :=
    memLp_one_iff_integrable.mp (hv.mul (hf n))
  have hpair := tendsto_integral_of_L1' (v * g) (Eventually.of_forall hi) hLp
  simpa only [Pi.mul_apply, mul_comm] using hpair

end RicciFlowSharpEstimate.Analysis
