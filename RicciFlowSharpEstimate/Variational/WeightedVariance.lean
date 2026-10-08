/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.PairFunctional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact weighted pair variance

The actual ordered-triangle quadratic form admits an exact centered identity.
The proof uses compact-domain Fubini and the fundamental theorem of calculus
applied to primitives, without differentiating the original profile.

The compact-triangle and slice arguments adapt the checked `PairFunctional`
and `PairIteration` modules by Ziyang Qin.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

/-- The weighted quadratic difference integral on the actual ordered triangle. -/
noncomputable def pairQuadratic (f : ℝ → ℝ) : ℝ :=
  ∫ p in orderedTriangle, 2 * p.2 * (f p.1 - f p.2) ^ 2

/-- The mean of a profile on the unit interval. -/
noncomputable def unitMean (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f x

/-- A profile centered by its actual unit-interval mean. -/
noncomputable def unitCentered (f : ℝ → ℝ) (x : ℝ) : ℝ := f x - unitMean f

/-- The actual primitive of the centered profile, based at zero. -/
noncomputable def centeredPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..x, unitCentered f v

private theorem continuousOn_prefix {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    ContinuousOn (fun x => ∫ v in (0 : ℝ)..x, f v) (Icc 0 1) := by
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ))
      (hf.intervalIntegrable_of_Icc zero_le_one) left_mem_uIcc

private theorem hasDerivAt_prefix {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => ∫ v in (0 : ℝ)..y, f v) (f x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hf.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2.le⟩)).intervalIntegrable_of_Icc hx.1.le
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono (fun y hy => ⟨hy.1.le, hy.2.le⟩)) x hx
  · exact hf.continuousAt (Icc_mem_nhds hx.1 hx.2)

/-- Centering preserves interval continuity. -/
theorem continuousOn_unitCentered (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ContinuousOn (unitCentered f) (Icc 0 1) :=
  hf.sub continuousOn_const

/-- The actual centered profile has mean zero. -/
theorem integral_unitCentered (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, unitCentered f x) = 0 := by
  change (∫ x in (0 : ℝ)..1, f x - unitMean f) = 0
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc zero_le_one)
    intervalIntegrable_const]
  simp [unitMean]

/-- The centered primitive is continuous up to both endpoints. -/
theorem continuousOn_centeredPrimitive (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) : ContinuousOn (centeredPrimitive f) (Icc 0 1) :=
  continuousOn_prefix (continuousOn_unitCentered f hf)

@[simp] theorem centeredPrimitive_zero (f : ℝ → ℝ) : centeredPrimitive f 0 = 0 := by
  simp [centeredPrimitive]

theorem centeredPrimitive_one (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    centeredPrimitive f 1 = 0 := integral_unitCentered f hf

private theorem integral_triangle_eq_iterated (F : ℝ × ℝ → ℝ)
    (hF : ContinuousOn F (Icc ((0 : ℝ), (0 : ℝ)) (1, 1))) :
    (∫ p in orderedTriangle, F p) = ∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..s, F (v, s) := by
  let W := orderedTriangle.indicator F
  have hW : Integrable W :=
    ((hF.integrableOn_compact isCompact_Icc).mono_set (by
      intro p hp
      exact ⟨⟨hp.1, hp.1.trans hp.2.1.le⟩, ⟨hp.2.1.le.trans hp.2.2, hp.2.2⟩⟩)).integrable_indicator
      measurableSet_orderedTriangle
  have hprod : Integrable W (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hW
  have hback : (fun s => ∫ t, W (t, s)) =
      (Icc 0 1).indicator (fun s => ∫ t in (0 : ℝ)..s, F (t, s)) := by
    funext s
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hs]
      have hslice : (fun t => W (t, s)) = (Ico 0 s).indicator (fun t => F (t, s)) := by
        funext t
        simp [W, orderedTriangle, indicator, hs.2]
      rw [hslice, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
        intervalIntegral.integral_of_le hs.1]
    · rw [indicator_of_notMem hs]
      have hzero : ∀ t, W (t, s) = 0 := by
        intro t
        apply indicator_of_notMem
        intro hp
        exact hs ⟨hp.1.trans hp.2.1.le, hp.2.2⟩
      simp only [hzero, integral_zero]
  calc
    (∫ p in orderedTriangle, F p) = ∫ p : ℝ × ℝ, W p :=
      (integral_indicator measurableSet_orderedTriangle).symm
    _ = ∫ s, ∫ t, W (t, s) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hprod
    _ = ∫ s in Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..s, F (t, s) := by
      rw [hback, integral_indicator measurableSet_Icc]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

private theorem pairQuadratic_eq_iterated (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    pairQuadratic f = ∫ s in (0 : ℝ)..1,
      ∫ v in (0 : ℝ)..s, 2 * s * (f v - f s) ^ 2 := by
  have hdiff : ContinuousOn (fun p : ℝ × ℝ => f p.1 - f p.2)
      (Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
    (hf.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)).sub
      (hf.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩))
  exact integral_triangle_eq_iterated _
    ((continuous_const.mul continuous_snd).continuousOn.mul (hdiff.pow 2))

private theorem inner_square_expansion (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..s, 2 * s * (g v - g s) ^ 2) =
      2 * s * (∫ v in (0 : ℝ)..s, (g v) ^ 2) -
        4 * s * g s * (∫ v in (0 : ℝ)..s, g v) + 2 * s ^ 2 * (g s) ^ 2 := by
  have hgc : ContinuousOn g (Icc 0 s) := hg.mono (fun v hv => ⟨hv.1, hv.2.trans hs.2⟩)
  have hgint := hgc.intervalIntegrable_of_Icc (μ := volume) hs.1
  have hg2int : IntervalIntegrable (fun v => (g v) ^ 2) volume 0 s :=
    (hgc.pow 2).intervalIntegrable_of_Icc hs.1
  calc
    (∫ v in (0 : ℝ)..s, 2 * s * (g v - g s) ^ 2) =
        ∫ v in (0 : ℝ)..s, 2 * s * (g v) ^ 2 - (4 * s * g s) * g v +
          2 * s * (g s) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hg2int.const_mul (2 * s)).sub
        (hgint.const_mul (4 * s * g s))) intervalIntegrable_const,
        intervalIntegral.integral_sub (hg2int.const_mul (2 * s))
          (hgint.const_mul (4 * s * g s)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring

private theorem pairQuadratic_eq_zeroMean_integrals (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (hzero : (∫ x in (0 : ℝ)..1, g x) = 0) :
    pairQuadratic g = (∫ x in (0 : ℝ)..1, (1 + x ^ 2) * (g x) ^ 2) +
      2 * (∫ x in (0 : ℝ)..1, (∫ v in (0 : ℝ)..x, g v) ^ 2) := by
  let G := fun x : ℝ => ∫ v in (0 : ℝ)..x, g v
  let H := fun x : ℝ => ∫ v in (0 : ℝ)..x, (g v) ^ 2
  let T := fun x : ℝ => 2 * x * H x - 4 * x * g x * G x + 2 * x ^ 2 * (g x) ^ 2
  let V := fun x : ℝ => (1 + x ^ 2) * (g x) ^ 2 + 2 * (G x) ^ 2
  let F := fun x : ℝ => (x ^ 2 - 1) * H x - 2 * x * (G x) ^ 2
  have hGcont : ContinuousOn G (Icc 0 1) := continuousOn_prefix hg
  have hHcont : ContinuousOn H (Icc 0 1) := continuousOn_prefix (hg.pow 2)
  have hTcont : ContinuousOn T (Icc 0 1) :=
    (((continuous_const.mul continuous_id).continuousOn.mul hHcont).sub
      (((continuous_const.mul continuous_id).continuousOn.mul hg).mul hGcont)).add
      ((continuous_const.mul (continuous_id.pow 2)).continuousOn.mul (hg.pow 2))
  have hBcont : ContinuousOn (fun x : ℝ => (1 + x ^ 2) * (g x) ^ 2) (Icc 0 1) :=
    (continuous_const.add (continuous_id.pow 2)).continuousOn.mul (hg.pow 2)
  have hVcont : ContinuousOn V (Icc 0 1) :=
    hBcont.add (continuousOn_const.mul (hGcont.pow 2))
  have hFcont : ContinuousOn F (Icc 0 1) :=
    (((continuous_id.pow 2).sub continuous_const).continuousOn.mul hHcont).sub
      ((continuous_const.mul continuous_id).continuousOn.mul (hGcont.pow 2))
  have hFderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (T x - V x) x := by
    intro x hx
    have hG := hasDerivAt_prefix hg x hx
    have hH := hasDerivAt_prefix (hg.pow 2) x hx
    apply (((((hasDerivAt_id x).pow 2).sub_const 1).mul hH).sub
      (((hasDerivAt_id x).const_mul 2).mul (hG.pow 2))).congr_deriv
    dsimp only [T, V, G, H, Pi.pow_apply, id_eq]
    ring
  have hF0 : F 0 = 0 := by simp [F, G, H]
  have hF1 : F 1 = 0 := by simp [F, G, H, hzero]
  have hTInt := hTcont.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hVInt := hVcont.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hFcont hFderiv ((hTcont.sub hVcont).intervalIntegrable_of_Icc zero_le_one)
  rw [hF0, hF1, sub_self, intervalIntegral.integral_sub hTInt hVInt] at hFTC
  have hTV : (∫ x in (0 : ℝ)..1, T x) = ∫ x in (0 : ℝ)..1, V x := sub_eq_zero.mp hFTC
  calc
    pairQuadratic g = ∫ s in (0 : ℝ)..1, T s := by
      rw [pairQuadratic_eq_iterated g hg]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact inner_square_expansion g hg s hs
    _ = ∫ x in (0 : ℝ)..1, V x := hTV
    _ = _ := by
      dsimp only [V]
      have hG2Int : IntervalIntegrable (fun x => 2 * (G x) ^ 2) volume 0 1 :=
        (continuousOn_const.mul (hGcont.pow 2)).intervalIntegrable_of_Icc zero_le_one
      rw [intervalIntegral.integral_add (hBcont.intervalIntegrable_of_Icc zero_le_one)
        hG2Int, intervalIntegral.integral_const_mul]

/-- Exact weighted variance identity for the actual ordered pair quadratic form. -/
theorem pairQuadratic_eq_centered_integrals (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) :
    pairQuadratic f =
      (∫ x in (0 : ℝ)..1, (1 + x ^ 2) * (unitCentered f x) ^ 2) +
        2 * (∫ x in (0 : ℝ)..1, (centeredPrimitive f x) ^ 2) := by
  have hinvariant : pairQuadratic f = pairQuadratic (unitCentered f) := by
    unfold pairQuadratic
    apply setIntegral_congr_fun measurableSet_orderedTriangle
    intro p hp
    dsimp only [unitCentered]
    ring
  rw [hinvariant]
  exact pairQuadratic_eq_zeroMean_integrals (unitCentered f)
    (continuousOn_unitCentered f hf) (integral_unitCentered f hf)

/-- The weighted pair quadratic form controls the actual centered L2 variance. -/
theorem integral_unitCentered_sq_le_pairQuadratic (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, (unitCentered f x) ^ 2) ≤ pairQuadratic f := by
  have hg := continuousOn_unitCentered f hf
  have hsq : IntervalIntegrable (fun x => (unitCentered f x) ^ 2) volume 0 1 :=
    (hg.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hweighted :
      IntervalIntegrable (fun x => (1 + x ^ 2) * (unitCentered f x) ^ 2) volume 0 1 :=
    ((continuous_const.add (continuous_id.pow 2)).continuousOn.mul
      (hg.pow 2)).intervalIntegrable_of_Icc zero_le_one
  have hle : (∫ x in (0 : ℝ)..1, (unitCentered f x) ^ 2) ≤
      ∫ x in (0 : ℝ)..1, (1 + x ^ 2) * (unitCentered f x) ^ 2 := by
    apply intervalIntegral.integral_mono_on zero_le_one hsq hweighted
    intro x hx
    have hprod := mul_nonneg (sq_nonneg x) (sq_nonneg (unitCentered f x))
    nlinarith
  have hprim : 0 ≤ ∫ x in (0 : ℝ)..1, (centeredPrimitive f x) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg _)
  rw [pairQuadratic_eq_centered_integrals f hf]
  linarith

end RicciFlowSharpEstimate.Variational
