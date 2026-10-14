/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.UnitIntervalGreen
import RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives

/-!
# Regularity of the actual weighted Green adjoints

The Dirichlet adjoint has a classical first derivative in the interior when
only the parabolic weight times its source is integrable. Its derivative is
the difference of the two actual weighted tails. The adjoint of the slope
kernel has the exact primitive formula for an integrable source.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem green_uIcc_subset {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩

private theorem green_left_integrable (A : ℝ → ℝ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (fun s => s * A s) volume 0 b := by
  have hI : IntervalIntegrable (fun s => s * (1 - s) * A s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hA
  have hsub : uIcc (0 : ℝ) b ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hb0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hb1.le
  have hInv : ContinuousOn (fun s : ℝ => (1 - s)⁻¹) (uIcc (0 : ℝ) b) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) b := by simpa only [uIcc_of_le hb0] using hs
    exact (sub_pos.mpr (hs'.2.trans_lt hb1)).ne'
  apply ((hI.mono_set hsub).mul_continuousOn hInv).congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) b := by
    simpa only [uIcc_of_le hb0] using uIoc_subset_uIcc hs
  have hne : 1 - s ≠ 0 := (sub_pos.mpr (hs'.2.trans_lt hb1)).ne'
  change (s * (1 - s) * A s) * (1 - s)⁻¹ = s * A s
  calc
    _ = (s * A s) * ((1 - s) * (1 - s)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne, mul_one]

private theorem green_right_integrable (A : ℝ → ℝ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun s => (1 - s) * A s) volume a 1 := by
  have hI : IntervalIntegrable (fun s => s * (1 - s) * A s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hA
  have hsub : uIcc a (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ha1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0.le le_rfl
  have hInv : ContinuousOn (fun s : ℝ => s⁻¹) (uIcc a (1 : ℝ)) := by
    apply continuous_id.continuousOn.inv₀
    intro s hs
    have hs' : s ∈ Icc a (1 : ℝ) := by simpa only [uIcc_of_le ha1] using hs
    exact (ha0.trans_le hs'.1).ne'
  apply ((hI.mono_set hsub).mul_continuousOn hInv).congr
  intro s hs
  have hs' : s ∈ Icc a (1 : ℝ) := by
    simpa only [uIcc_of_le ha1] using uIoc_subset_uIcc hs
  have hne : s ≠ 0 := (ha0.trans_le hs'.1).ne'
  change (s * (1 - s) * A s) * s⁻¹ = (1 - s) * A s
  calc
    _ = ((1 - s) * A s) * (s * s⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne, mul_one]

private theorem green_kernel_integrable (A : ℝ → ℝ)
    (hAm : AEStronglyMeasurable A areaμ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun s => unitDirichletKernel s x * A s) areaμ := by
  have hk : Continuous (fun s => unitDirichletKernel s x) :=
    continuous_unitDirichletKernel.comp (continuous_id.prodMk continuous_const)
  apply hA.mono (hk.aestronglyMeasurable.mul hAm)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  rw [abs_of_nonneg hs.1.le, abs_of_nonneg (sub_nonneg.mpr hs.2.le)]
  exact mul_le_mul_of_nonneg_right
    (abs_unitDirichletKernel_le s x (Ioo_subset_Icc_self hs) hx) (abs_nonneg (A s))

private theorem green_tail_formula (A : ℝ → ℝ)
    (hAm : AEStronglyMeasurable A areaμ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ s, unitDirichletKernel s x * A s ∂areaμ) =
      (1 - x) * (∫ s in (0 : ℝ)..x, s * A s) +
        x * (∫ s in x..1, (1 - s) * A s) := by
  have hI : IntervalIntegrable (fun s => unitDirichletKernel s x * A s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
      (green_kernel_integrable A hAm hA (Ioo_subset_Icc_self hx))
  have hL : IntervalIntegrable (fun s => unitDirichletKernel s x * A s) volume 0 x :=
    hI.mono_set (by
      rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2.le)
  have hR : IntervalIntegrable (fun s => unitDirichletKernel s x * A s) volume x 1 :=
    hI.mono_set (by
      rw [uIcc_of_le hx.2.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx.1.le le_rfl)
  have hLeq : (∫ s in (0 : ℝ)..x, unitDirichletKernel s x * A s) =
      (1 - x) * ∫ s in (0 : ℝ)..x, s * A s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) x := by simpa only [uIcc_of_le hx.1.le] using hs
    change (min s x - s * x) * A s = (1 - x) * (s * A s)
    rw [min_eq_left hs'.2]
    ring
  have hReq : (∫ s in x..1, unitDirichletKernel s x * A s) =
      x * ∫ s in x..1, (1 - s) * A s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc x (1 : ℝ) := by simpa only [uIcc_of_le hx.2.le] using hs
    change (min s x - s * x) * A s = x * ((1 - s) * A s)
    rw [min_eq_right hs'.1]
    ring
  calc
    _ = ∫ s in (0 : ℝ)..1, unitDirichletKernel s x * A s := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    _ = (∫ s in (0 : ℝ)..x, unitDirichletKernel s x * A s) +
        ∫ s in x..1, unitDirichletKernel s x * A s :=
      (intervalIntegral.integral_add_adjacent_intervals hL hR).symm
    _ = _ := by rw [hLeq, hReq]

private theorem green_right_primitive (F : ℝ → ℝ) {a x : ℝ} (ha : a ≤ 1)
    (hF : IntervalIntegrable F volume a 1) (hx : x ∈ Icc a (1 : ℝ)) :
    (∫ s in x..1, F s) = (∫ s in a..1, F s) - ∫ s in a..x, F s := by
  have hL : IntervalIntegrable F volume a x := hF.mono_set (by
    rw [uIcc_of_le hx.1, uIcc_of_le ha]
    exact Icc_subset_Icc le_rfl hx.2)
  have hR : IntervalIntegrable F volume x 1 := hF.mono_set (by
    rw [uIcc_of_le hx.2, uIcc_of_le ha]
    exact Icc_subset_Icc hx.1 le_rfl)
  linarith only [intervalIntegral.integral_add_adjacent_intervals hL hR]

private theorem green_local_data (A : ℝ → ℝ)
    (hAm : AEStronglyMeasurable A areaμ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    let G := fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ
    let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
    AbsolutelyContinuousOnInterval G a b ∧ AbsolutelyContinuousOnInterval J a b ∧
      ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt G (J x) x ∧ HasDerivAt J (-A x) x := by
  let L : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, s * A s
  let R : ℝ → ℝ := fun x => ∫ s in x..1, (1 - s) * A s
  let G : ℝ → ℝ := fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ
  let J : ℝ → ℝ := fun x => R x - L x
  change AbsolutelyContinuousOnInterval G a b ∧ AbsolutelyContinuousOnInterval J a b ∧
    ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt G (J x) x ∧ HasDerivAt J (-A x) x
  have ha1 : a < 1 := hab.trans hb
  have hb0 : 0 < b := ha.trans hab
  have hLI := green_left_integrable A hA hb0.le hb
  have hRI := green_right_integrable A hA ha ha1.le
  have ha0b : a ∈ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hb0.le]
    exact ⟨ha.le, hab.le⟩
  have hba1 : b ∈ uIcc a (1 : ℝ) := by
    rw [uIcc_of_le ha1.le]
    exact ⟨hab.le, hb.le⟩
  have hLAC : AbsolutelyContinuousOnInterval L a b :=
    (hLI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).mono
      (uIcc_subset_uIcc ha0b (by simp))
  have hPAC : AbsolutelyContinuousOnInterval
      (fun x => ∫ s in a..x, (1 - s) * A s) a b :=
    (hRI.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).mono
      (uIcc_subset_uIcc (by simp) hba1)
  have hConst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => ∫ s in a..1, (1 - s) * A s) a b := by
    have hCD : ContDiff ℝ 1 (fun _ : ℝ => ∫ s in a..1, (1 - s) * A s) := contDiff_const
    exact hCD.contDiffOn.absolutelyContinuousOnInterval
  have hRAC : AbsolutelyContinuousOnInterval R a b := by
    apply (hConst.fun_sub hPAC).congr
    intro x hx
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hx
    exact (green_right_primitive (fun s => (1 - s) * A s) ha1.le hRI
      ⟨hx'.1, hx'.2.trans hb.le⟩).symm
  have hId : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
    (contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
  have hOne : AbsolutelyContinuousOnInterval (fun x : ℝ => 1 - x) a b := by
    have hCD : ContDiff ℝ 1 (fun x : ℝ => 1 - x) := contDiff_const.sub contDiff_id
    exact hCD.contDiffOn.absolutelyContinuousOnInterval
  have hGAC : AbsolutelyContinuousOnInterval G a b := by
    apply ((hOne.fun_mul hLAC).fun_add (hId.fun_mul hRAC)).congr
    intro x hx
    exact (green_tail_formula A hAm hA
      (green_uIcc_subset ⟨ha, ha1⟩ ⟨hb0, hb⟩ hx)).symm
  refine ⟨hGAC, hRAC.fun_sub hLAC, ?_⟩
  filter_upwards [hLI.ae_hasDerivAt_integral, hRI.ae_hasDerivAt_integral] with x hxL hxR
  intro hx
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hx0b : x ∈ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hb0.le]
    exact ⟨hx01.1.le, hx.2.le⟩
  have hxa1 : x ∈ uIcc a (1 : ℝ) := by
    rw [uIcc_of_le ha1.le]
    exact ⟨hx.1.le, hx01.2.le⟩
  have hLD : HasDerivAt L (x * A x) x := hxL hx0b 0 (by simp)
  have hRD : HasDerivAt R (-((1 - x) * A x)) x := by
    have hBase : HasDerivAt
        (fun y => (∫ s in a..1, (1 - s) * A s) - ∫ s in a..y, (1 - s) * A s)
        (-((1 - x) * A x)) x :=
      (hxR hxa1 a (by simp)).const_sub (∫ s in a..1, (1 - s) * A s)
    apply hBase.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo a (1 : ℝ) from ⟨hx.1, hx01.2⟩)] with y hy
    exact green_right_primitive (fun s => (1 - s) * A s) ha1.le hRI ⟨hy.1.le, hy.2.le⟩
  have hJD : HasDerivAt J (-A x) x := by
    change HasDerivAt (fun y => R y - L y) (-A x) x
    convert hRD.sub hLD using 1
    ring
  have hGD : HasDerivAt (fun y => (1 - y) * L y + y * R y) (J x) x := by
    have hProd := (((hasDerivAt_id x).const_sub 1).mul hLD).add
      ((hasDerivAt_id x).mul hRD)
    have hProd' : HasDerivAt (fun y => (1 - y) * L y + y * R y)
        ((-1) * L x + (1 - x) * (x * A x) +
          (1 * R x + x * (-((1 - x) * A x)))) x := by
      simpa only [Pi.add_def, Pi.mul_def, id_eq] using hProd
    have hValue : (-1) * L x + (1 - x) * (x * A x) +
        (1 * R x + x * (-((1 - x) * A x))) = J x := by
      dsimp only [J]
      ring
    rw [hValue] at hProd'
    exact hProd'
  refine ⟨hGD.congr_of_eventuallyEq ?_, hJD⟩
  filter_upwards [isOpen_Ioo.mem_nhds hx01] with y hy
  exact green_tail_formula A hAm hA hy

private theorem green_ae_of_local {P : ℝ → Prop}
    (hP : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      ∀ᵐ x ∂volume, x ∈ Ioo a b → P x) : ∀ᵐ x ∂areaμ, P x := by
  have hRat : ∀ q : ℚ × ℚ, ∀ᵐ x ∂volume,
      0 < (q.1 : ℝ) → (q.1 : ℝ) < q.2 → (q.2 : ℝ) < 1 →
        x ∈ Ioo (q.1 : ℝ) (q.2 : ℝ) → P x := by
    intro q
    by_cases ha : 0 < (q.1 : ℝ)
    · by_cases hab : (q.1 : ℝ) < q.2
      · by_cases hb : (q.2 : ℝ) < 1
        · filter_upwards [hP q.1 q.2 ha hab hb] with x hx
          exact fun _ _ _ => hx
        · exact Eventually.of_forall fun _ _ _ h => (hb h).elim
      · exact Eventually.of_forall fun _ _ h => (hab h).elim
    · exact Eventually.of_forall fun _ h => (ha h).elim
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [ae_all_iff.2 hRat] with x hx
  intro hxI
  obtain ⟨a, ha, hax⟩ := exists_rat_btwn hxI.1
  obtain ⟨b, hxb, hb⟩ := exists_rat_btwn hxI.2
  exact hx (a, b) ha (hax.trans hxb) hb ⟨hax, hxb⟩

private theorem green_continuousOn_of_local_ac (F : ℝ → ℝ)
    (hF : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval F a b) : ContinuousOn F (Ioo (0 : ℝ) 1) := by
  intro x hx
  let a := x / 2
  let b := (x + 1) / 2
  have ha : a ∈ Ioo (0 : ℝ) 1 := by dsimp [a]; constructor <;> linarith [hx.1, hx.2]
  have hb : b ∈ Ioo (0 : ℝ) 1 := by dsimp [b]; constructor <;> linarith [hx.1, hx.2]
  have hax : a < x := by dsimp [a]; linarith only [hx.1]
  have hxb : x < b := by dsimp [b]; linarith only [hx.2]
  have hN : uIcc a b ∈ 𝓝 x := by
    rw [uIcc_of_le (hax.trans hxb).le]
    exact Icc_mem_nhds hax hxb
  exact ((hF a ha b hb).continuousOn.continuousAt hN).continuousWithinAt

private theorem green_classical_derivative (G J : ℝ → ℝ)
    (hJ : ContinuousOn J (Ioo (0 : ℝ) 1))
    (hG : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval G a b)
    (hD : ∀ᵐ x ∂areaμ, HasDerivAt G (J x) x) :
    ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (J x) x := by
  have hDfull := (ae_restrict_iff' measurableSet_Ioo).1 hD
  have hFTC (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      (∫ t in x..y, J t) = G y - G x := by
    have h := (hG x hx y hy).integral_deriv_eq_sub
    have heq : (∫ t in x..y, deriv G t) = ∫ t in x..y, J t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hDfull] with t ht htI
      exact (ht (green_uIcc_subset hx hy (uIoc_subset_uIcc htI))).deriv
    rw [heq] at h
    exact h
  intro x hx
  have hJM : StronglyMeasurableAtFilter J (𝓝 x) volume :=
    ⟨Ioo (0 : ℝ) 1, isOpen_Ioo.mem_nhds hx,
      (hJ.locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable⟩
  have hDeriv := (intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable J volume x x from IntervalIntegrable.refl)
    hJM (hJ.continuousAt (isOpen_Ioo.mem_nhds hx))).const_add (G x)
  apply hDeriv.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  have hxy := hFTC x hx y hy
  linarith only [hxy]

/-- The actual Dirichlet adjoint is C¹ in the interior under weighted source
integrability alone. Its classical derivative is the actual weighted tail
difference, which is locally absolutely continuous with derivative `-A` almost
everywhere. No unweighted endpoint integrability or independent jet is assumed. -/
theorem weighted_dirichlet_adjoint_local_regularity (A : ℝ → ℝ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ) :
    let G := fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ
    let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
    (∀ x ∈ Ioo (0 : ℝ) 1,
      IntervalIntegrable (fun s => s * A s) volume 0 x ∧
      IntervalIntegrable (fun s => (1 - s) * A s) volume x 1 ∧
      Integrable (fun s => unitDirichletKernel s x * A s) areaμ ∧
      G x = (1 - x) * (∫ s in (0 : ℝ)..x, s * A s) +
        x * (∫ s in x..1, (1 - s) * A s)) ∧
    ContDiffOn ℝ 1 G (Ioo (0 : ℝ) 1) ∧ ContinuousOn J (Ioo (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (J x) x) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval G a b ∧ AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ x ∂areaμ, HasDerivAt J (-A x) x) := by
  have hweight : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hAm : AEStronglyMeasurable A areaμ := by
    apply (hA.aestronglyMeasurable.div₀ hweight).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_div_cancel_left₀ (A x) (mul_pos hx.1 (sub_pos.mpr hx.2)).ne'
  let G : ℝ → ℝ := fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ
  let J : ℝ → ℝ := fun x =>
    (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  have hlocal (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :=
    green_local_data A hAm hA a b ha hab hb
  have hAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval G a b ∧ AbsolutelyContinuousOnInterval J a b := by
    rcases lt_trichotomy a b with hab | hab | hba
    · exact ⟨(hlocal a b ha.1 hab hb.2).1, (hlocal a b ha.1 hab hb.2).2.1⟩
    · subst b
      exact ⟨AbsolutelyContinuousOnInterval.refl G a, AbsolutelyContinuousOnInterval.refl J a⟩
    · exact ⟨(hlocal b a hb.1 hba ha.2).1.symm, (hlocal b a hb.1 hba ha.2).2.1.symm⟩
  have hJC : ContinuousOn J (Ioo (0 : ℝ) 1) :=
    green_continuousOn_of_local_ac J (fun a ha b hb => (hAC a ha b hb).2)
  have hDeriv : ∀ᵐ x ∂areaμ, HasDerivAt G (J x) x ∧ HasDerivAt J (-A x) x :=
    green_ae_of_local (fun a b ha hab hb => (hlocal a b ha hab hb).2.2)
  have hGD : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (J x) x :=
    green_classical_derivative G J hJC (fun a ha b hb => (hAC a ha b hb).1)
      (hDeriv.mono fun _ hx => hx.1)
  have hGC1 : ContDiffOn ℝ 1 G (Ioo (0 : ℝ) 1) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
    refine ⟨fun x hx => (hGD x hx).differentiableAt.differentiableWithinAt, ?_⟩
    apply hJC.congr
    intro x hx
    exact (hGD x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)
  refine ⟨?_, hGC1, hJC, hGD, hAC, hDeriv.mono fun _ hx => hx.2⟩
  intro x hx
  exact ⟨green_left_integrable A hA hx.1.le hx.2,
    green_right_integrable A hA hx.1 hx.2.le,
    green_kernel_integrable A hAm hA (Ioo_subset_Icc_self hx), green_tail_formula A hAm hA hx⟩

/-- The adjoint of the actual slope kernel is the primitive of the source
minus its total integral times the coordinate. It is absolutely continuous
on the closed physical interval, vanishes at both endpoints, and has the
corresponding derivative almost everywhere. The diagonal is handled modulo
its zero measure; no smoothness of the source is assumed. -/
theorem slope_kernel_adjoint_absolutelyContinuous (B : ℝ → ℝ)
    (hB : Integrable B areaμ) :
    let H := fun x => ∫ s, unitDirichletSlopeKernel s x * B s ∂areaμ
    (∀ x ∈ Icc (0 : ℝ) 1,
      H x = (∫ s in (0 : ℝ)..x, B s) - x * ∫ s in (0 : ℝ)..1, B s) ∧
    AbsolutelyContinuousOnInterval H 0 1 ∧ H 0 = 0 ∧ H 1 = 0 ∧
    (∀ᵐ x ∂areaμ, HasDerivAt H (B x - ∫ s in (0 : ℝ)..1, B s) x) := by
  let H : ℝ → ℝ := fun x => ∫ s, unitDirichletSlopeKernel s x * B s ∂areaμ
  have hI : IntervalIntegrable B volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hB
  have hFormula (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      H x = (∫ s in (0 : ℝ)..x, B s) - x * ∫ s in (0 : ℝ)..1, B s := by
    have hInd : IntervalIntegrable ((Iic x).indicator B) volume 0 1 :=
      ⟨hI.1.indicator measurableSet_Iic, hI.2.indicator measurableSet_Iic⟩
    have hne : ∀ᵐ s ∂volume, s ≠ x := by simp [ae_iff, measure_singleton]
    have heq : (∫ s in (0 : ℝ)..1, unitDirichletSlopeKernel s x * B s) =
        ∫ s in (0 : ℝ)..1, (Iic x).indicator B s - x * B s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hne] with s hs _
      by_cases hsx : s ≤ x
      · have hslt : s < x := lt_of_le_of_ne hsx hs
        rw [unitDirichletSlopeKernel, ite_eq_right (not_le.mpr hslt),
          indicator_of_mem (show s ∈ Iic x from hsx)]
        ring
      · have hxs : x ≤ s := le_of_not_ge hsx
        rw [unitDirichletSlopeKernel, ite_eq_left hxs,
          indicator_of_notMem (show s ∉ Iic x from hsx)]
        ring
    calc
      H x = ∫ s in (0 : ℝ)..1, unitDirichletSlopeKernel s x * B s := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      _ = ∫ s in (0 : ℝ)..1, (Iic x).indicator B s - x * B s := heq
      _ = _ := by
        have hIndicator : (∫ s in (0 : ℝ)..1, (Iic x).indicator B s) =
            ∫ s in (0 : ℝ)..x, B s := intervalIntegral.integral_indicator hx
        rw [intervalIntegral.integral_sub hInd (hI.const_mul x),
          intervalIntegral.integral_const_mul, hIndicator]
  have hP : AbsolutelyContinuousOnInterval (fun x => ∫ s in (0 : ℝ)..x, B s) 0 1 :=
    hI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hAffine : AbsolutelyContinuousOnInterval
      (fun x : ℝ => x * ∫ s in (0 : ℝ)..1, B s) 0 1 := by
    have hCD : ContDiff ℝ 1 (fun x : ℝ => x * ∫ s in (0 : ℝ)..1, B s) :=
      contDiff_id.mul contDiff_const
    exact hCD.contDiffOn.absolutelyContinuousOnInterval
  have hAC : AbsolutelyContinuousOnInterval H 0 1 := by
    apply (hP.fun_sub hAffine).congr
    intro x hx
    exact (hFormula x (by simpa only [uIcc_of_le zero_le_one] using hx)).symm
  have hZero : H 0 = 0 := by rw [hFormula 0 (by norm_num)]; simp
  have hOne : H 1 = 0 := by rw [hFormula 1 (by norm_num)]; simp
  refine ⟨hFormula, hAC, hZero, hOne, ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hI.ae_hasDerivAt_integral] with x hx
  intro hxI
  have hxC : x ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self hxI
  have hD := (hx hxC 0 (by simp)).sub
    ((hasDerivAt_id x).mul_const (∫ s in (0 : ℝ)..1, B s))
  have hD' : HasDerivAt
      (fun y => (∫ s in (0 : ℝ)..y, B s) - y * ∫ s in (0 : ℝ)..1, B s)
      (B x - ∫ s in (0 : ℝ)..1, B s) x := by
    simpa only [Pi.sub_def, id_eq, one_mul] using hD
  apply hD'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
  exact hFormula y (Ioo_subset_Icc_self hy)

end RicciFlowSharpEstimate.Analysis
