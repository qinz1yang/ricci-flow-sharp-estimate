/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Uniform L2 integrability from bounded interiors and square tails

A family with uniformly bounded square integrals is uniformly L2 integrable
if, for every small tolerance, all its members are uniformly bounded on one
measurable set and have square integral at most that tolerance on its
complement. The set and the bound may depend on the tolerance.

On a finite measure space, almost-everywhere convergence of such a sequence
therefore gives a square-integrable limit and convergence in L2.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem eLpNorm_two_le_of_integral_sq_le
    {h : α → ℝ} (hh : MemLp h 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hI : (∫ x, h x ^ 2 ∂μ) ≤ C ^ 2) :
    eLpNorm h 2 μ ≤ ENNReal.ofReal C := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hh]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    ← one_div, ← Real.sqrt_eq_rpow] using
    (ENNReal.ofReal_le_ofReal ((Real.sqrt_le_left hC).mpr hI))

/-- A uniform square-integral bound passes to an almost-everywhere limit,
so the limit is genuinely in L² even without uniform integrability. -/
theorem memLp_two_of_ae_tendsto_of_integral_sq_bound
    (f : ℕ → α → ℝ) (g : α → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ x, f n x ^ 2 ∂μ) ≤ M)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    MemLp g 2 μ := by
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => sq_nonneg (f 0 x))).trans (hM 0)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable) hfg
  have hb (n : ℕ) : eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (Real.sqrt M) :=
    eLpNorm_two_le_of_integral_sq_le (hf n) (Real.sqrt_nonneg M)
      (by simpa only [Real.sq_sqrt hM0] using hM n)
  have hlim := Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hb)
    (fun n => (hf n).aestronglyMeasurable) hg hfg
  exact hlim.trans_lt ENNReal.ofReal_lt_top

/-- Uniformly bounded square integrals, together with uniformly bounded
values on measurable sets having arbitrarily small complementary square
tails, imply native uniform L2 integrability. The measure need not be finite. -/
theorem uniformIntegrable_two_of_sq_tails
    (f : ℕ → α → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ x, f n x ^ 2 ∂μ) ≤ M)
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ S : Set α, MeasurableSet S ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ n, (∀ᵐ x ∂μ, x ∈ S → |f n x| ≤ B) ∧
          (∫ x in Sᶜ, f n x ^ 2 ∂μ) ≤ ε) :
    UniformIntegrable f 2 μ := by
  have hhigh : ∀ ε : ENNReal, 0 < ε → ∃ C : NNReal,
      ∀ n, eLpNorm ({x | C ≤ ‖f n x‖₊}.indicator (f n)) 2 μ ≤ ε := by
    intro ε hε
    by_cases htop : ε = ⊤
    · refine ⟨0, fun n ↦ ?_⟩
      rw [htop]
      exact le_top
    have hεreal : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
    obtain ⟨S, hS, B, hB, hcontrol⟩ := htails (ε.toReal ^ 2) (sq_pos_of_pos hεreal)
    let C : NNReal := ⟨B + 1, by linarith⟩
    refine ⟨C, ?_⟩
    intro n
    let A : Set α := {x | C ≤ ‖f n x‖₊}
    have hA : NullMeasurableSet A μ :=
      aestronglyMeasurable_const.nullMeasurableSet_le (hf n).aestronglyMeasurable.nnnorm
    change eLpNorm (A.indicator (f n)) 2 μ ≤ ε
    calc
      eLpNorm (A.indicator (f n)) 2 μ ≤ eLpNorm (Sᶜ.indicator (f n)) 2 μ := by
        apply eLpNorm_mono_ae ((hf n).aestronglyMeasurable.indicator₀ hA)
        filter_upwards [(hcontrol n).1] with x hx
        by_cases hxA : x ∈ A
        · have hxS : x ∉ S := by
            intro hxS
            have hnorm : B + 1 ≤ ‖f n x‖ := hxA
            rw [Real.norm_eq_abs] at hnorm
            linarith [hx hxS]
          have hxSc : x ∈ Sᶜ := hxS
          rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxSc]
        · rw [Set.indicator_of_notMem hxA, norm_zero]
          exact norm_nonneg _
      _ = eLpNorm (f n) 2 (μ.restrict Sᶜ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hS.compl
      _ ≤ ENNReal.ofReal ε.toReal :=
        eLpNorm_two_le_of_integral_sq_le ((hf n).restrict Sᶜ) hεreal.le (hcontrol n).2
      _ = ε := ENNReal.ofReal_toReal htop
  refine ⟨unifIntegrable_of (by norm_num) (by simp)
    (fun n ↦ (hf n).aestronglyMeasurable) hhigh, ?_⟩
  have hMnonneg : 0 ≤ M :=
    (integral_nonneg (fun x ↦ sq_nonneg (f 0 x))).trans (hM 0)
  refine ⟨⟨Real.sqrt M, Real.sqrt_nonneg M⟩, fun n ↦ ?_⟩
  have hbound := eLpNorm_two_le_of_integral_sq_le (hf n) (Real.sqrt_nonneg M)
    (by simpa only [Real.sq_sqrt hMnonneg] using hM n)
  convert hbound using 1
  exact (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg M)).symm

/-- Almost-everywhere convergence, a uniform square-integral bound, and the
bounded-interior/small-square-tail criterion give a square-integrable limit
and strong L2 convergence on a finite measure space. -/
theorem memLp_and_tendsto_eLpNorm_two_of_sq_tails [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (M : ℝ) (hM : ∀ n, (∫ x, f n x ^ 2 ∂μ) ≤ M)
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ S : Set α, MeasurableSet S ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ n, (∀ᵐ x ∂μ, x ∈ S → |f n x| ≤ B) ∧
          (∫ x in Sᶜ, f n x ^ 2 ∂μ) ≤ ε)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (nhds (g x))) :
    MemLp g 2 μ ∧ Tendsto (fun n ↦ eLpNorm (f n - g) 2 μ) atTop (nhds 0) := by
  have hUI : UniformIntegrable f 2 μ := uniformIntegrable_two_of_sq_tails f hf M hM htails
  have hg : MemLp g 2 μ := hUI.memLp_of_ae_tendsto hfg
  refine ⟨hg, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by simp)
    (fun n ↦ (hf n).aestronglyMeasurable) hg hUI.unifIntegrable hfg

end RicciFlowSharpEstimate.Analysis
