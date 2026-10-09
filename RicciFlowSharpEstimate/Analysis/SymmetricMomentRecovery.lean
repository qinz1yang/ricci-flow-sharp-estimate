/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SymmetricBernstein
import RicciFlowSharpEstimate.Analysis.L1Subsequence
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Symmetric monotone smooth recovery with exact moments

The approximation reserves a strict box margin before making the actual constant
correction to the zeroth moment. The prescribed closed box is unchanged.
The construction is adapted from Ziyang Qin's historical exact-moment Bernstein recovery.
-/

noncomputable section

open Filter MeasureTheory Set Topology

open scoped unitInterval ContDiff

namespace RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery

private def HasShape (K : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x) ∧
    MonotoneOn K (Icc (1 / 2 : ℝ) 1)

private def momentZero (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, f x
private def momentOne (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, x * f x

/-- Reflection about the midpoint fixes the first moment at one half of the zeroth moment. -/
theorem firstMoment_eq_half_integral_of_reflection
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hsymm : ∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = f x) :
    (∫ x in (0 : ℝ)..1, x * f x) = (∫ x in (0 : ℝ)..1, f x) / 2 := by
  have hxf : IntervalIntegrable (fun x => x * f x) volume 0 1 :=
    hf.continuousOn_mul continuousOn_id
  have hsubst := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) (fun x => x * f x) 1
  have heq : (∫ x in (0 : ℝ)..1, x * f x) =
      (∫ x in (0 : ℝ)..1, f x) - ∫ x in (0 : ℝ)..1, x * f x := by
    calc
      (∫ x in (0 : ℝ)..1, x * f x) =
          ∫ x in (0 : ℝ)..1, (1 - x) * f (1 - x) := by
        simpa only [sub_self, sub_zero] using hsubst.symm
      _ = ∫ x in (0 : ℝ)..1, f x - x * f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
        dsimp only
        rw [hsymm x hx']
        ring
      _ = _ := intervalIntegral.integral_sub hf hxf
  linarith

private def symmetricBernsteinMomentCorrection
    (target : ℝ) (n : ℕ) (K : ℝ → ℝ) : ℝ :=
  target - momentZero (symmetricBernsteinApproximation n K) 0 1

private def momentCorrectedSymmetricBernsteinApproximation
    (target : ℝ) (n : ℕ) (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  symmetricBernsteinApproximation n K x +
    symmetricBernsteinMomentCorrection target n K

private theorem contDiff_momentCorrectedSymmetricBernsteinApproximation
    (target : ℝ) (n : ℕ) (K : ℝ → ℝ) :
    ContDiff ℝ ∞
      (momentCorrectedSymmetricBernsteinApproximation target n K) := by
  exact (contDiff_symmetricBernsteinApproximation n K).add contDiff_const

private theorem momentZero_momentCorrectedSymmetricBernsteinApproximation
    (target : ℝ) (n : ℕ) (K : ℝ → ℝ) :
    momentZero
      (momentCorrectedSymmetricBernsteinApproximation target n K) 0 1 =
      target := by
  have hA : IntervalIntegrable
      (symmetricBernsteinApproximation n K) MeasureTheory.volume 0 1 :=
    (contDiff_symmetricBernsteinApproximation n K).continuous.intervalIntegrable 0 1
  unfold momentCorrectedSymmetricBernsteinApproximation
    symmetricBernsteinMomentCorrection momentZero
  rw [intervalIntegral.integral_add hA
    (continuous_const.intervalIntegrable 0 1)]
  simp

private theorem symmetricMonotone_momentCorrectedSymmetricBernsteinApproximation
    (target : ℝ) (n : ℕ) (K : ℝ → ℝ)
    (hK : MonotoneOn K (Icc (1 / 2 : ℝ) 1)) :
    HasShape (momentCorrectedSymmetricBernsteinApproximation target n K) := by
  constructor
  · intro x hx
    unfold momentCorrectedSymmetricBernsteinApproximation
    rw [symmetric_symmetricBernsteinApproximation n K x]
  · intro x hx y hy hxy
    unfold momentCorrectedSymmetricBernsteinApproximation
    simpa only [add_comm] using add_le_add_right
      (monotoneOn_symmetricBernsteinApproximation n K hK hx hy hxy)
      (symmetricBernsteinMomentCorrection target n K)

private def strictInteriorMix
    (target eta : ℝ) (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - eta) * K x + eta * target

private theorem symmetricMonotone_strictInteriorMix
    (target eta : ℝ) (hEta : eta ≤ 1)
    (K : ℝ → ℝ) (hK : HasShape K) :
    HasShape (strictInteriorMix target eta K) := by
  have hScale : 0 ≤ 1 - eta := sub_nonneg.mpr hEta
  constructor
  · intro x hx
    unfold strictInteriorMix
    rw [hK.1 x hx]
  · intro x hx y hy hxy
    unfold strictInteriorMix
    simpa only [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (hK.2 hx hy hxy) hScale) (eta * target)

private def strictInteriorMargin
    (target lo hi eta : ℝ) : ℝ :=
  eta * min (target - lo) (hi - target)

private theorem strictInteriorMargin_pos
    (target lo hi eta : ℝ) (hEta : 0 < eta)
    (hTargetLower : lo < target) (hTargetUpper : target < hi) :
    0 < strictInteriorMargin target lo hi eta := by
  unfold strictInteriorMargin
  exact mul_pos hEta (lt_min (sub_pos.mpr hTargetLower)
    (sub_pos.mpr hTargetUpper))

private theorem strictInteriorMix_mem_strictBox
    (target lo hi eta : ℝ) (hEta0 : 0 ≤ eta) (hEta1 : eta ≤ 1)
    (K : ℝ → ℝ)
    (hKbox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      strictInteriorMix target eta K x ∈
        Icc
          (lo + strictInteriorMargin target lo hi eta)
          (hi - strictInteriorMargin target lo hi eta) := by
  intro x hx
  have hKx := hKbox x hx
  have hRemain : 0 ≤ 1 - eta := sub_nonneg.mpr hEta1
  have hLowerTerm : 0 ≤ (1 - eta) * (K x - lo) :=
    mul_nonneg hRemain (sub_nonneg.mpr hKx.1)
  have hUpperTerm : 0 ≤ (1 - eta) * (hi - K x) :=
    mul_nonneg hRemain (sub_nonneg.mpr hKx.2)
  have hMarginLower :
      strictInteriorMargin target lo hi eta ≤ eta * (target - lo) := by
    unfold strictInteriorMargin
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hEta0
  have hMarginUpper :
      strictInteriorMargin target lo hi eta ≤ eta * (hi - target) := by
    unfold strictInteriorMargin
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hEta0
  unfold strictInteriorMix
  constructor <;> nlinarith

private theorem tendsto_symmetricBernsteinApproximation_apply_of_radialContinuousWithinAt
    (K : ℝ → ℝ) (lo hi : ℝ)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi)
    (hSymm : ∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x)
    (x : I)
    (hContinuous : ContinuousWithinAt (upperRadialProfile K)
      (Icc (0 : ℝ) 1) (squaredMidpointRadius x)) :
    Tendsto (fun n : ℕ => symmetricBernsteinApproximation n K x)
      atTop (𝓝 (K x)) := by
  have hBound : ∀ y ∈ Icc (0 : ℝ) 1,
      |upperRadialProfile K y| ≤ max |lo| |hi| := by
    intro y hy
    have hyArg : (1 + Real.sqrt y) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hsqrt : Real.sqrt y ≤ 1 := Real.sqrt_le_one.2 hy.2
        linarith
    exact abs_le_max_abs_abs (hBox _ hyArg).1 (hBox _ hyArg).2
  have h := tendsto_sampledBernsteinPolynomial (upperRadialProfile K) hBound
    (squaredMidpointRadius_mem_Icc x.property) hContinuous
  simpa only [symmetricBernsteinApproximation,
    upperRadialProfile_squaredMidpointRadius_eq K hSymm x.property] using h

private theorem countable_radialPreimage
    (s : Set ℝ) (hs : s.Countable) :
    {x : I | squaredMidpointRadius x ∈ s}.Countable := by
  let lower : Set I :=
    {x : I | (x : ℝ) ≤ 1 / 2 ∧ squaredMidpointRadius x ∈ s}
  let upper : Set I :=
    {x : I | 1 / 2 ≤ (x : ℝ) ∧ squaredMidpointRadius x ∈ s}
  have hLowerMaps : MapsTo
      (fun x : I => squaredMidpointRadius x) lower s := by
    intro x hx
    exact hx.2
  have hLowerInj : Set.InjOn
      (fun x : I => squaredMidpointRadius x) lower := by
    intro x hx y hy hxy
    dsimp only [lower, Set.mem_ofPred_eq] at hx hy
    apply Subtype.ext
    unfold squaredMidpointRadius at hxy
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hxy with hSame | hOpposite
    · linarith
    · linarith [hx.1, hy.1]
  have hLowerCountable : lower.Countable :=
    hLowerMaps.countable_of_injOn hLowerInj hs
  have hUpperMaps : MapsTo
      (fun x : I => squaredMidpointRadius x) upper s := by
    intro x hx
    exact hx.2
  have hUpperInj : Set.InjOn
      (fun x : I => squaredMidpointRadius x) upper := by
    intro x hx y hy hxy
    dsimp only [upper, Set.mem_ofPred_eq] at hx hy
    apply Subtype.ext
    unfold squaredMidpointRadius at hxy
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hxy with hSame | hOpposite
    · linarith
    · linarith [hx.1, hy.1]
  have hUpperCountable : upper.Countable :=
    hUpperMaps.countable_of_injOn hUpperInj hs
  apply (hLowerCountable.union hUpperCountable).mono
  intro x hx
  rcases le_total (x : ℝ) (1 / 2 : ℝ) with hxHalf | hxHalf
  · exact Or.inl ⟨hxHalf, hx⟩
  · exact Or.inr ⟨hxHalf, hx⟩

/-- For a bounded symmetric-monotone profile, its smooth symmetric
Bernstein approximants converge pointwise almost everywhere. -/
private theorem ae_tendsto_symmetricBernsteinApproximation
    (K : ℝ → ℝ) (lo hi : ℝ)
    (hClass : HasShape K)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi) :
    ∀ᵐ (x : I) ∂(volume : Measure I),
      Tendsto (fun n : ℕ => symmetricBernsteinApproximation n K x)
        atTop (𝓝 (K x)) := by
  let bad : Set ℝ :=
    {t ∈ Icc (0 : ℝ) 1 |
      ¬ContinuousWithinAt (upperRadialProfile K) (Icc (0 : ℝ) 1) t}
  have hBadCountable : bad.Countable := by
    exact
      (monotoneOn_upperRadialProfile K hClass.2).countable_not_continuousWithinAt
  have hBadPreimage :
      {x : I | squaredMidpointRadius x ∈ bad}.Countable :=
    countable_radialPreimage bad hBadCountable
  filter_upwards [hBadPreimage.ae_notMem (volume : Measure I)] with x hx
  apply tendsto_symmetricBernsteinApproximation_apply_of_radialContinuousWithinAt
    K lo hi hBox hClass.1 x
  by_contra hNotContinuous
  exact hx ⟨squaredMidpointRadius_mem_Icc x.property, hNotContinuous⟩

private theorem integral_unitInterval_eq_momentZero (f : ℝ → ℝ) :
    (∫ x : I, f x ∂(volume : Measure I)) = momentZero f 0 1 := by
  unfold momentZero
  calc
    (∫ x : I, f x ∂(volume : Measure I)) =
        ∫ x : ℝ in Icc (0 : ℝ) 1, f x :=
      integral_subtype measurableSet_Icc f
    _ = ∫ x : ℝ in Ioc (0 : ℝ) 1, f x := integral_Icc_eq_integral_Ioc
    _ = ∫ x : ℝ in (0 : ℝ)..1, f x := by
      rw [intervalIntegral.integral_of_le zero_le_one]

private theorem integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
    (f : ℝ → ℝ) (lo hi : ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => f x))
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc lo hi) :
    Integrable (fun x : I => f x) (volume : Measure I) := by
  apply integrable_of_le_of_le hMeasurable.aestronglyMeasurable
  · filter_upwards with x
    exact (hBox x x.property).1
  · filter_upwards with x
    exact (hBox x x.property).2
  · exact integrable_const lo
  · exact integrable_const hi

private theorem stronglyMeasurable_strictInteriorMix
    (target eta : ℝ) (K : ℝ → ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => K x)) :
    StronglyMeasurable (fun x : I => strictInteriorMix target eta K x) := by
  unfold strictInteriorMix
  exact (hMeasurable.const_mul (1 - eta)).add stronglyMeasurable_const

private theorem momentZero_strictInteriorMix_of_stronglyMeasurable
    (target lo hi eta : ℝ) (K : ℝ → ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => K x))
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi)
    (hMoment : momentZero K 0 1 = target) :
    momentZero (strictInteriorMix target eta K) 0 1 = target := by
  have hKIntegrable : Integrable (fun x : I => K x) :=
    integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
      K lo hi hMeasurable hBox
  have hMomentI : (∫ x : I, K x ∂(volume : Measure I)) = target := by
    rw [integral_unitInterval_eq_momentZero, hMoment]
  rw [← integral_unitInterval_eq_momentZero]
  change (∫ x : I, (1 - eta) * K x + eta * target
    ∂(volume : Measure I)) = target
  rw [integral_add (hKIntegrable.const_mul (1 - eta))
    (integrable_const (eta * target)), integral_const_mul, hMomentI]
  simp
  ring

/-- The symmetric Bernstein approximants of a bounded measurable
symmetric-monotone profile converge in `L1` on the unit interval. -/
private theorem tendsto_integral_abs_symmetricBernsteinApproximation_sub_zero
    (K : ℝ → ℝ) (lo hi : ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => K x))
    (hClass : HasShape K)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi) :
    Tendsto (fun n : ℕ => ∫ x : I,
      |symmetricBernsteinApproximation n K x - K x|
        ∂(volume : Measure I)) atTop (𝓝 0) := by
  have hIntegral : Tendsto (fun n : ℕ => ∫ x : I,
      |symmetricBernsteinApproximation n K x - K x|
        ∂(volume : Measure I)) atTop
      (𝓝 (∫ _x : I, (0 : ℝ) ∂(volume : Measure I))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : I => hi - lo)
    · intro n
      have hSmooth : StronglyMeasurable
          (fun x : I => symmetricBernsteinApproximation n K x) :=
        ((contDiff_symmetricBernsteinApproximation n K).continuous.comp
          continuous_subtype_val).stronglyMeasurable
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (hSmooth.sub hMeasurable).norm.aestronglyMeasurable
    · exact integrable_const (hi - lo)
    · intro n
      filter_upwards with x
      have hRawBox := symmetricBernsteinApproximation_mem_Icc
        n K lo hi hBox x.property
      have hKBox := hBox x x.property
      rw [Real.norm_eq_abs, abs_abs]
      apply (abs_le).2
      constructor <;> linarith [hRawBox.1, hRawBox.2, hKBox.1, hKBox.2]
    · filter_upwards
        [ae_tendsto_symmetricBernsteinApproximation K lo hi hClass hBox]
        with x hx
      have hDifference : Tendsto
          (fun n : ℕ => symmetricBernsteinApproximation n K x - K x)
          atTop (𝓝 (K x - K x)) :=
        hx.sub tendsto_const_nhds
      have hAbsolute := hDifference.abs
      simpa only [sub_self, abs_zero] using hAbsolute
  simpa using hIntegral

/-- The scalar correction imposing the exact zeroth moment tends to zero
also for a possibly discontinuous bounded symmetric-monotone target. -/
private theorem symmetricBernsteinMomentCorrection_tendsto_zero_of_bounded_symmetricMonotone
    (target : ℝ) (K : ℝ → ℝ) (lo hi : ℝ)
    (hClass : HasShape K)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi)
    (hMoment : momentZero K 0 1 = target) :
    Tendsto (fun n : ℕ => symmetricBernsteinMomentCorrection target n K)
      atTop (𝓝 0) := by
  let bound : I → ℝ := fun _ => max |lo| |hi|
  have hIntegral : Tendsto (fun n : ℕ => ∫ x : I,
      symmetricBernsteinApproximation n K x ∂(volume : Measure I))
      atTop (𝓝 (∫ x : I, K x ∂(volume : Measure I))) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro n
      exact ((contDiff_symmetricBernsteinApproximation n K).continuous.comp
        continuous_subtype_val).stronglyMeasurable.aestronglyMeasurable
    · exact integrable_const (max |lo| |hi|)
    · intro n
      filter_upwards with x
      have hRawBox := symmetricBernsteinApproximation_mem_Icc
        n K lo hi hBox x.property
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs hRawBox.1 hRawBox.2
    · exact ae_tendsto_symmetricBernsteinApproximation
        K lo hi hClass hBox
  have hMomentTendsto : Tendsto
      (fun n : ℕ => momentZero (symmetricBernsteinApproximation n K) 0 1)
      atTop (𝓝 target) := by
    simpa only [integral_unitInterval_eq_momentZero, hMoment] using hIntegral
  have hTarget : Tendsto (fun _ : ℕ => target) atTop (𝓝 target) :=
    tendsto_const_nhds
  simpa only [symmetricBernsteinMomentCorrection, sub_self] using
    hTarget.sub hMomentTendsto

/-- Every bounded measurable symmetric-monotone function with the prescribed mean
admits smooth symmetric-monotone approximants with both exact moments in the
same closed box, arbitrarily close in `L1`. -/
private theorem exists_smooth_symmetricMonotone_exactMoments_mem_box_integral_close
    (target lo hi : ℝ) (hTargetLower : lo < target)
    (hTargetUpper : target < hi)
    (K : ℝ → ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => K x))
    (hClass : HasShape K)
    (hMoment : momentZero K 0 1 = target)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ G : ℝ → ℝ,
      ContDiff ℝ ∞ G ∧
        HasShape G ∧
        (∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc lo hi) ∧
        momentZero G 0 1 = target ∧
        momentOne G 0 1 = (1 / 2 : ℝ) * target ∧
        (∫ x : I, |G x - K x| ∂(volume : Measure I)) < epsilon := by
  have hWidth : 0 < hi - lo := by linarith
  have hEtaUpper : 0 < min (1 : ℝ) (epsilon / (hi - lo)) :=
    lt_min zero_lt_one (div_pos hEpsilon hWidth)
  obtain ⟨eta, hEtaPos, hEtaLt⟩ := exists_between hEtaUpper
  have hEtaOne : eta ≤ 1 :=
    (hEtaLt.trans_le (min_le_left _ _)).le
  have hEtaError : eta * (hi - lo) < epsilon := by
    exact (lt_div_iff₀ hWidth).1
      (hEtaLt.trans_le (min_le_right _ _))
  let rho := epsilon - eta * (hi - lo)
  have hRho : 0 < rho := by
    unfold rho
    linarith
  let Keta := strictInteriorMix target eta K
  have hKetaMeasurable : StronglyMeasurable (fun x : I => Keta x) :=
    stronglyMeasurable_strictInteriorMix target eta K hMeasurable
  have hKetaClass : HasShape Keta :=
    symmetricMonotone_strictInteriorMix target eta hEtaOne K hClass
  have hKetaMoment : momentZero Keta 0 1 = target :=
    momentZero_strictInteriorMix_of_stronglyMeasurable
      target lo hi eta K hMeasurable hBox hMoment
  let delta := strictInteriorMargin target lo hi eta
  have hDelta : 0 < delta :=
    strictInteriorMargin_pos target lo hi eta hEtaPos
      hTargetLower hTargetUpper
  have hKetaStrictBox : ∀ x ∈ Icc (0 : ℝ) 1,
      Keta x ∈ Icc (lo + delta) (hi - delta) := by
    exact strictInteriorMix_mem_strictBox target lo hi eta hEtaPos.le
      hEtaOne K hBox
  have hRawTendsto :=
    tendsto_integral_abs_symmetricBernsteinApproximation_sub_zero
      Keta (lo + delta) (hi - delta) hKetaMeasurable
      hKetaClass hKetaStrictBox
  have hCorrectionTendsto :=
    symmetricBernsteinMomentCorrection_tendsto_zero_of_bounded_symmetricMonotone
      target Keta (lo + delta) (hi - delta) hKetaClass
      hKetaStrictBox hKetaMoment
  let totalError : ℕ → ℝ := fun n =>
    (∫ x : I, |symmetricBernsteinApproximation n Keta x - Keta x|
      ∂(volume : Measure I)) +
      |symmetricBernsteinMomentCorrection target n Keta|
  have hTotalError : Tendsto totalError atTop (𝓝 0) := by
    simpa only [totalError, abs_zero, zero_add] using
      hRawTendsto.add hCorrectionTendsto.abs
  have hEventuallyError : ∀ᶠ n : ℕ in atTop, totalError n < rho :=
    (tendsto_order.1 hTotalError).2 rho hRho
  have hEventuallyBox : ∀ᶠ n : ℕ in atTop, ∀ x : I,
      momentCorrectedSymmetricBernsteinApproximation target n Keta x ∈
        Icc lo hi := by
    have hCorrectionAbs : Tendsto
        (fun n : ℕ => |symmetricBernsteinMomentCorrection target n Keta|)
        atTop (𝓝 0) := by
      simpa only [abs_zero] using hCorrectionTendsto.abs
    have hEventuallyCorrection : ∀ᶠ n : ℕ in atTop,
        |symmetricBernsteinMomentCorrection target n Keta| < delta :=
      (tendsto_order.1 hCorrectionAbs).2 delta hDelta
    filter_upwards [hEventuallyCorrection] with n hn
    intro x
    have hRaw := symmetricBernsteinApproximation_mem_Icc
      n Keta (lo + delta) (hi - delta) hKetaStrictBox x.property
    have hCorr := (abs_lt.1 hn)
    rcases hRaw with ⟨hRawLower, hRawUpper⟩
    unfold momentCorrectedSymmetricBernsteinApproximation
    constructor <;> linarith
  obtain ⟨n, hBoxN, hErrorN⟩ :=
    (hEventuallyBox.and hEventuallyError).exists
  let G := momentCorrectedSymmetricBernsteinApproximation target n Keta
  have hGSmooth : ContDiff ℝ ∞ G :=
    contDiff_momentCorrectedSymmetricBernsteinApproximation target n Keta
  have hGClass : HasShape G :=
    symmetricMonotone_momentCorrectedSymmetricBernsteinApproximation
      target n Keta hKetaClass.2
  have hGBox : ∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc lo hi := by
    intro x hx
    exact hBoxN ⟨x, hx⟩
  have hGZero : momentZero G 0 1 = target :=
    momentZero_momentCorrectedSymmetricBernsteinApproximation target n Keta
  have hGOne : momentOne G 0 1 = (1 / 2 : ℝ) * target := by
    change (∫ x in (0 : ℝ)..1, x * G x) = (1 / 2 : ℝ) * target
    rw [firstMoment_eq_half_integral_of_reflection G
      (hGSmooth.continuous.intervalIntegrable 0 1) hGClass.1]
    change momentZero G 0 1 / 2 = (1 / 2 : ℝ) * target
    rw [hGZero]
    ring
  have hKIntegrable : Integrable (fun x : I => K x) :=
    integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
      K lo hi hMeasurable hBox
  have hKetaIntegrable : Integrable (fun x : I => Keta x) :=
    integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
      Keta (lo + delta) (hi - delta) hKetaMeasurable hKetaStrictBox
  have hRawMeasurable : StronglyMeasurable
      (fun x : I => symmetricBernsteinApproximation n Keta x) :=
    ((contDiff_symmetricBernsteinApproximation n Keta).continuous.comp
      continuous_subtype_val).stronglyMeasurable
  have hRawIntegrable : Integrable
      (fun x : I => symmetricBernsteinApproximation n Keta x) :=
    integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
      (symmetricBernsteinApproximation n Keta)
      (lo + delta) (hi - delta) hRawMeasurable
      (fun x hx => symmetricBernsteinApproximation_mem_Icc
        n Keta (lo + delta) (hi - delta) hKetaStrictBox hx)
  have hRawDifferenceIntegrable : Integrable (fun x : I =>
      |symmetricBernsteinApproximation n Keta x - Keta x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hRawIntegrable.sub hKetaIntegrable).norm
  have hMixDifferenceIntegrable : Integrable (fun x : I =>
      |Keta x - K x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hKetaIntegrable.sub hKIntegrable).norm
  have hTargetBox : target ∈ Icc lo hi :=
    ⟨hTargetLower.le, hTargetUpper.le⟩
  have hMixPointwise : ∀ x : I,
      |Keta x - K x| ≤ eta * (hi - lo) := by
    intro x
    have hKx := hBox x x.property
    have hTargetSub : |target - K x| ≤ hi - lo := by
      apply (abs_le).2
      constructor <;>
        linarith [hKx.1, hKx.2, hTargetBox.1, hTargetBox.2]
    unfold Keta strictInteriorMix
    rw [show (1 - eta) * K x + eta * target - K x =
      eta * (target - K x) by ring]
    rw [abs_mul, abs_of_pos hEtaPos]
    exact mul_le_mul_of_nonneg_left hTargetSub hEtaPos.le
  have hMixIntegral :
      (∫ x : I, |Keta x - K x| ∂(volume : Measure I)) ≤
        eta * (hi - lo) := by
    calc
      (∫ x : I, |Keta x - K x| ∂(volume : Measure I)) ≤
          ∫ _x : I, eta * (hi - lo) ∂(volume : Measure I) :=
        integral_mono hMixDifferenceIntegrable
          (integrable_const (eta * (hi - lo))) hMixPointwise
      _ = eta * (hi - lo) := by simp
  have hPointwise : ∀ x : I,
      |G x - K x| ≤
        (|symmetricBernsteinApproximation n Keta x - Keta x| +
          |symmetricBernsteinMomentCorrection target n Keta|) +
        |Keta x - K x| := by
    intro x
    unfold G momentCorrectedSymmetricBernsteinApproximation
    calc
      |symmetricBernsteinApproximation n Keta x +
          symmetricBernsteinMomentCorrection target n Keta - K x| =
          |((symmetricBernsteinApproximation n Keta x - Keta x) +
            symmetricBernsteinMomentCorrection target n Keta) +
            (Keta x - K x)| := by ring_nf
      _ ≤ |(symmetricBernsteinApproximation n Keta x - Keta x) +
            symmetricBernsteinMomentCorrection target n Keta| +
            |Keta x - K x| := abs_add_le _ _
      _ ≤ (|symmetricBernsteinApproximation n Keta x - Keta x| +
            |symmetricBernsteinMomentCorrection target n Keta|) +
            |Keta x - K x| := by
        gcongr
        exact abs_add_le _ _
  have hUpperIntegrable : Integrable (fun x : I =>
      (|symmetricBernsteinApproximation n Keta x - Keta x| +
        |symmetricBernsteinMomentCorrection target n Keta|) +
      |Keta x - K x|) :=
    (hRawDifferenceIntegrable.add
      (integrable_const |symmetricBernsteinMomentCorrection target n Keta|)).add
      hMixDifferenceIntegrable
  have hIntegralTriangle :
      (∫ x : I, |G x - K x| ∂(volume : Measure I)) ≤
        ∫ x : I,
          (|symmetricBernsteinApproximation n Keta x - Keta x| +
            |symmetricBernsteinMomentCorrection target n Keta|) +
          |Keta x - K x| ∂(volume : Measure I) := by
    apply integral_mono_of_nonneg
    · filter_upwards with x
      positivity
    · exact hUpperIntegrable
    · filter_upwards with x
      exact hPointwise x
  refine ⟨G, hGSmooth, hGClass, hGBox, hGZero, hGOne, ?_⟩
  calc
    (∫ x : I, |G x - K x| ∂(volume : Measure I)) ≤
        ∫ x : I,
          (|symmetricBernsteinApproximation n Keta x - Keta x| +
            |symmetricBernsteinMomentCorrection target n Keta|) +
          |Keta x - K x| ∂(volume : Measure I) := hIntegralTriangle
    _ = ((∫ x : I,
          |symmetricBernsteinApproximation n Keta x - Keta x|
            ∂(volume : Measure I)) +
          |symmetricBernsteinMomentCorrection target n Keta|) +
        ∫ x : I, |Keta x - K x| ∂(volume : Measure I) := by
      have hsplit := integral_add
        (hRawDifferenceIntegrable.add
          (integrable_const |symmetricBernsteinMomentCorrection target n Keta|))
        hMixDifferenceIntegrable
      simp only [Pi.add_apply] at hsplit
      rw [hsplit, integral_add hRawDifferenceIntegrable
        (integrable_const |symmetricBernsteinMomentCorrection target n Keta|)]
      simp
    _ ≤ totalError n + eta * (hi - lo) := by
      simpa only [totalError, add_comm, add_left_comm, add_assoc] using
        add_le_add_left hMixIntegral (totalError n)
    _ < rho + eta * (hi - lo) := by
      simpa only [add_comm] using
        add_lt_add_right hErrorN (eta * (hi - lo))
    _ = epsilon := by
      unfold rho
      ring

private theorem antitoneOn_of_shape (f : ℝ → ℝ) (hf : HasShape f) :
    AntitoneOn f (Icc (0 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  have hx' : 1 - x ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : 1 - y ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := hf.2 hy' hx' (by linarith)
  rw [hf.1 y ⟨hy.1, by linarith [hy.2]⟩,
    hf.1 x ⟨hx.1, by linarith [hx.2]⟩] at h
  exact h

/-- A bounded measurable symmetric profile, monotone from the midpoint to the
right endpoint, has globally smooth approximants with both exact moments and
both hemisphere order laws in the identical closed box. They converge in `L1`
and admit an almost-everywhere convergent strictly increasing subsequence. -/
theorem exists_smooth_exactMoments_mem_box_l1_ae
    (m lo hi : ℝ) (hLower : lo < m) (hUpper : m < hi)
    (K : ℝ → ℝ)
    (hMeasurable : StronglyMeasurable (fun x : I => K x))
    (hSymm : ∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x)
    (hMono : MonotoneOn K (Icc (1 / 2 : ℝ) 1))
    (hMoment : (∫ x in (0 : ℝ)..1, K x) = m)
    (hBox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi) :
    ∃ G : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (G n) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, G n (1 - x) = G n x) ∧
        MonotoneOn (G n) (Icc (1 / 2 : ℝ) 1) ∧
        AntitoneOn (G n) (Icc (0 : ℝ) (1 / 2)) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, G n x ∈ Icc lo hi) ∧
        (∫ x in (0 : ℝ)..1, G n x) = m ∧
        (∫ x in (0 : ℝ)..1, x * G n x) = m / 2) ∧
      Tendsto (fun n => ∫ x in (0 : ℝ)..1, |G n x - K x|) atTop (𝓝 0) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
          Tendsto (fun n => G (ns n) x) atTop (𝓝 (K x)) := by
  have hExists : ∀ n : ℕ, ∃ G : ℝ → ℝ,
      ContDiff ℝ ∞ G ∧ HasShape G ∧
      (∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc lo hi) ∧
      momentZero G 0 1 = m ∧ momentOne G 0 1 = (1 / 2 : ℝ) * m ∧
      (∫ x : I, |G x - K x| ∂(volume : Measure I)) <
        1 / ((n : ℝ) + 1) := by
    intro n
    exact exists_smooth_symmetricMonotone_exactMoments_mem_box_integral_close
      m lo hi hLower hUpper K hMeasurable ⟨hSymm, hMono⟩ hMoment hBox
      (by positivity)
  choose G hSmooth hShape hBoxG hZero hOne hClose using hExists
  have hL1Subtype : Tendsto
      (fun n => ∫ x : I, |G n x - K x| ∂(volume : Measure I)) atTop (𝓝 0) := by
    have hNonnegative : ∀ᶠ n in atTop,
        0 ≤ ∫ x : I, |G n x - K x| ∂(volume : Measure I) :=
      Filter.Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _
    have hUpperBound : ∀ᶠ n in atTop,
        (∫ x : I, |G n x - K x| ∂(volume : Measure I)) ≤
          1 / ((n : ℝ) + 1) :=
      Filter.Eventually.of_forall fun n => (hClose n).le
    exact squeeze_zero' hNonnegative hUpperBound
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |G n x - K x|)
      atTop (𝓝 0) := by
    have hBridge : ∀ n, (∫ x : I, |G n x - K x| ∂(volume : Measure I)) =
        ∫ x in (0 : ℝ)..1, |G n x - K x| := fun n =>
      integral_unitInterval_eq_momentZero (fun x => |G n x - K x|)
    simpa only [hBridge] using hL1Subtype
  have hKIntegrable : Integrable (fun x : I => K x) (volume : Measure I) :=
    integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
      K lo hi hMeasurable hBox
  have hDifference : ∀ n, Integrable (fun x => G n x - K x)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    intro n
    have hGIntegrable : Integrable (fun x : I => G n x) (volume : Measure I) :=
      integrable_unitInterval_of_stronglyMeasurable_of_mem_Icc
        (G n) lo hi
        ((hSmooth n).continuous.comp continuous_subtype_val).stronglyMeasurable (hBoxG n)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2
      (hGIntegrable.sub hKIntegrable)
  have hNorm : Tendsto
      (fun n => ∫ x, ‖G n x - K x‖ ∂(volume.restrict (Icc (0 : ℝ) 1)))
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc, Real.norm_eq_abs] using hL1
  obtain ⟨ns, hns, hae⟩ :=
    L1Subsequence.exists_strictMono_ae_tendsto_of_integral_norm_tendsto_zero
      (volume.restrict (Icc (0 : ℝ) 1)) G K hDifference hNorm
  refine ⟨G, ?_, hL1, ns, hns, hae⟩
  intro n
  refine ⟨hSmooth n, (hShape n).1, (hShape n).2,
    antitoneOn_of_shape (G n) (hShape n), hBoxG n, hZero n, ?_⟩
  simpa [momentOne, div_eq_mul_inv, mul_comm] using hOne n

end RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery
