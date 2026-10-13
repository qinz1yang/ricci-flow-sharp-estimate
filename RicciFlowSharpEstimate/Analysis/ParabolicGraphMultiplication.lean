/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence
import RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra

/-!
# Smooth multiplication in the parabolic weak graph

Multiplication by a fixed globally smooth function preserves the actual
parabolic weak derivative graph and its strong topology. The weak product
rule follows by testing with the product of the original compactly supported
test and the smooth multiplier. The weighted graph coordinates are finite
sums of continuous coefficients times the original graph coordinates; the
coefficients are bounded on the closed physical interval.

The convergence theorem uses the actual derivatives of the multiplied
`C²` probes and the product jets of their given weak graph limit. No endpoint
condition or extra uniform bound is required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped ContDiff Topology

private theorem weakDerivOn_mul_contDiff
    {U : Set ℝ} {r p : ℝ → ℝ} (hU : IsOpen U)
    (h : HasWeakDerivOn U r p) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasWeakDerivOn U (fun x ↦ r x * u x)
      (fun x ↦ p x * u x + r x * deriv u x) := by
  have hrU := h.locallyIntegrable.mul_continuousOn
    hu.continuous.continuousOn hU.isLocallyClosed
  have hpU := h.locallyIntegrable_deriv.mul_continuousOn
    hu.continuous.continuousOn hU.isLocallyClosed
  have hrD := h.locallyIntegrable.mul_continuousOn
    (hu.continuous_deriv (by simp)).continuousOn hU.isLocallyClosed
  refine ⟨hrU, hpU.add hrD, ?_⟩
  intro φ hφ hφc hφU
  have htest := h.integral_deriv_mul (fun x ↦ φ x * u x) (hφ.mul hu)
    hφc.mul_right (tsupport_mul_subset_left.trans hφU)
  have hi₁ : Integrable (fun x ↦ deriv φ x * (r x * u x)) volume :=
    integrable_mul_of_locallyIntegrableOn hrU (hφ.continuous_deriv (by simp))
      hφc.deriv (tsupport_deriv_subset.trans hφU)
  have hi₂ : Integrable (fun x ↦ φ x * (r x * deriv u x)) volume :=
    integrable_mul_of_locallyIntegrableOn hrD hφ.continuous hφc hφU
  have hi₃ : Integrable (fun x ↦ φ x * (p x * u x)) volume :=
    integrable_mul_of_locallyIntegrableOn hpU hφ.continuous hφc hφU
  have hleft : (fun x ↦ deriv (fun y ↦ φ y * u y) x * r x) =
      (fun x ↦ deriv φ x * (r x * u x)) +
        (fun x ↦ φ x * (r x * deriv u x)) := by
    funext x
    rw [deriv_fun_mul (hφ.differentiable (by simp) x)
      (hu.differentiable (by simp) x)]
    simp only [Pi.add_apply]
    ring
  have hright : (fun x ↦ (φ x * u x) * p x) =
      (fun x ↦ φ x * (p x * u x)) := by
    funext x
    ring
  rw [hleft, hright] at htest
  change (∫ x, deriv φ x * (r x * u x) + φ x * (r x * deriv u x)) =
    -(∫ x, φ x * (p x * u x)) at htest
  rw [integral_add hi₁ hi₂] at htest
  have hsum : (fun x ↦ φ x * (p x * u x + r x * deriv u x)) =
      (fun x ↦ φ x * (p x * u x)) +
        (fun x ↦ φ x * (r x * deriv u x)) := by
    funext x
    simp only [Pi.add_apply, mul_add]
  rw [hsum]
  change (∫ x, deriv φ x * (r x * u x)) =
    -(∫ x, φ x * (p x * u x) + φ x * (r x * deriv u x))
  rw [integral_add hi₃ hi₂]
  linarith

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem ae_abs_le_of_continuous_Icc
    {a : ℝ → ℝ} (ha : Continuous a) :
    ∃ C : ℝ, ∀ᵐ x ∂areaμ, |a x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) ha.continuousOn
  refine ⟨C, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs] using hC x (Ioo_subset_Icc_self hx)

private theorem memLp_mul_continuous_Ioo
    {a f : ℝ → ℝ} (ha : Continuous a) (hf : MemLp f 2 areaμ) :
    MemLp (fun x ↦ a x * f x) 2 areaμ := by
  obtain ⟨C, hC⟩ := ae_abs_le_of_continuous_Icc ha
  exact memLp_mul_of_ae_abs_le ha.aestronglyMeasurable hC hf

private theorem strong_L2_mul_continuous_Ioo
    {f : ℕ → ℝ → ℝ} {f0 a : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 areaμ) (hf0 : MemLp f0 2 areaμ)
    (hstrong : Tendsto (fun n ↦ eLpNorm (f n - f0) 2 areaμ) atTop (𝓝 0))
    (ha : Continuous a) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ a x * f n x - a x * f0 x) 2 areaμ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := ae_abs_le_of_continuous_Icc ha
  have hmul := strong_L2_mul_of_ae_tendsto_of_ae_abs_le
    (a := fun _ ↦ a) (a0 := a) hf hf0 hstrong
    (fun _ ↦ ha.aestronglyMeasurable) ha.aestronglyMeasurable
    (fun _ ↦ hC) hC (Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  exact hmul.2.2

private theorem strong_L2_add
    {f g : ℕ → ℝ → ℝ} {f0 g0 : ℝ → ℝ}
    (hf : Tendsto (fun n ↦ eLpNorm (f n - f0) 2 areaμ) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ eLpNorm (g n - g0) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm ((f n + g n) - (f0 + g0)) 2 areaμ)
      atTop (𝓝 0) := by
  have hsumRaw := hf.add hg
  have hsum : Tendsto
      (fun n ↦ eLpNorm (f n - f0) 2 areaμ + eLpNorm (g n - g0) 2 areaμ)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hsumRaw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) ?_
  intro n
  have heq : (f n + g n) - (f0 + g0) = (f n - f0) + (g n - g0) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  dsimp only
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- Multiplication by a fixed globally smooth function preserves both
genuine weak derivatives and all three weighted `L²` conditions in the
parabolic graph. Its derivative representatives are the exact product jets. -/
theorem HasParabolicWeakDerivatives.mul_contDiff
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasParabolicWeakDerivatives
      (fun x ↦ r x * u x)
      (fun x ↦ p x * u x + r x * deriv u x)
      (fun x ↦ z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x) := by
  have huD : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have huDD : Continuous (deriv (deriv u)) := huD.continuous_deriv (by simp)
  have hw : Continuous (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  have hsecond := (weakDerivOn_mul_contDiff isOpen_Ioo h.weakDeriv_deriv u hu).add
    (weakDerivOn_mul_contDiff isOpen_Ioo h.weakDeriv (deriv u) huD)
  refine ⟨weakDerivOn_mul_contDiff isOpen_Ioo h.weakDeriv u hu,
    hsecond.congr_ae ae_eq_rfl ?_, ?_, ?_, ?_⟩
  · filter_upwards [] with x
    ring
  · refine (memLp_congr_ae ?_).1 (memLp_mul_continuous_Ioo hu.continuous h.memLp)
    filter_upwards [] with x
    ring
  · have h₁ := memLp_mul_continuous_Ioo hu.continuous h.memLp_weighted_deriv
    have h₂ := memLp_mul_continuous_Ioo (hw.sqrt.mul huD.continuous) h.memLp
    refine (memLp_congr_ae ?_).1 (h₁.add h₂)
    filter_upwards [] with x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · have h₁ := memLp_mul_continuous_Ioo hu.continuous h.memLp_weighted_secondDeriv
    have hc₂ : Continuous (fun x : ℝ ↦ 2 * (x * (1 - x)) * deriv u x) := by
      exact (continuous_const.mul hw).mul huD.continuous
    have h₂ := memLp_mul_continuous_Ioo hc₂ h.memLp_weighted_deriv
    have h₃ := memLp_mul_continuous_Ioo ((hw.mul hw.sqrt).mul huDD) h.memLp
    refine (memLp_congr_ae ?_).1 ((h₁.add h₂).add h₃)
    filter_upwards [] with x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring

/-- Multiplication by a fixed globally smooth function preserves all three
strong parabolic graph limits for actual `C²` probes. The limiting product
jets come from the supplied genuine weak derivative graph. -/
theorem parabolicGraph_tendsto_mul_contDiff
    {rn : ℕ → ℝ → ℝ} {r p z : ℝ → ℝ}
    (hrn : ∀ n, ContDiff ℝ 2 (rn n))
    (hgraph : HasParabolicWeakDerivatives r p z)
    (hR : Tendsto (fun n ↦ eLpNorm (rn n - r) 2 areaμ) atTop (𝓝 0))
    (hP : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (rn n) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0))
    (hZ : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rn n)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
      atTop (𝓝 0))
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ rn n x * u x) - (fun x ↦ r x * u x)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (fun y ↦ rn n y * u y) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * (p x * u x + r x * deriv u x)))
      2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
        deriv (deriv (fun y ↦ rn n y * u y)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
          (z x * u x + 2 * p x * deriv u x + r x * deriv (deriv u) x)))
      2 areaμ) atTop (𝓝 0) := by
  have huD : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have huDD : Continuous (deriv (deriv u)) := huD.continuous_deriv (by simp)
  have hw : Continuous (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  have hgraphs (n : ℕ) := hasParabolicWeakDerivatives_of_contDiff (hrn n)
  have hRmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp) hgraph.memLp hR hu.continuous
  have hPmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp_weighted_deriv)
    hgraph.memLp_weighted_deriv hP hu.continuous
  have hPRmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp) hgraph.memLp hR (hw.sqrt.mul huD.continuous)
  have hPsum := strong_L2_add hPmul hPRmul
  have hZmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp_weighted_secondDeriv)
    hgraph.memLp_weighted_secondDeriv hZ hu.continuous
  have hc₂ : Continuous (fun x : ℝ ↦ 2 * (x * (1 - x)) * deriv u x) := by
    exact (continuous_const.mul hw).mul huD.continuous
  have hZPmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp_weighted_deriv)
    hgraph.memLp_weighted_deriv hP hc₂
  have hZRmul := strong_L2_mul_continuous_Ioo
    (fun n ↦ (hgraphs n).memLp) hgraph.memLp hR ((hw.mul hw.sqrt).mul huDD)
  have hZsum := strong_L2_add (strong_L2_add hZmul hZPmul) hZRmul
  have hd (n : ℕ) : deriv (fun x ↦ rn n x * u x) =
      (fun x ↦ deriv (rn n) x * u x + rn n x * deriv u x) := by
    funext x
    exact deriv_fun_mul ((hrn n).differentiable (by norm_num) x)
      (hu.differentiable (by simp) x)
  have hdd (n : ℕ) : deriv (deriv (fun x ↦ rn n x * u x)) =
      (fun x ↦ deriv (deriv (rn n)) x * u x +
        2 * deriv (rn n) x * deriv u x + rn n x * deriv (deriv u) x) := by
    rw [hd n]
    funext x
    convert ((((hrn n).differentiable_deriv_two x).hasDerivAt.mul
      (hu.differentiable (by simp) x).hasDerivAt).add
      (((hrn n).differentiable (by norm_num) x).hasDerivAt.mul
        (huD.differentiable (by simp) x).hasDerivAt)).deriv using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · apply hRmul.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  · apply hPsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, hd]
    ring
  · apply hZsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, hdd]
    ring

end RicciFlowSharpEstimate.Analysis
