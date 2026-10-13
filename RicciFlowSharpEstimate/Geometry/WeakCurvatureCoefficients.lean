/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Geometry.AreaCurvatureVariation
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers

/-!
# Weak curvature coefficients of the complete area action

The coefficients retain the actual curvature primitives and weak meridional
operator. A recoverable competitor supplies a genuine weak derivative graph.
Its graph weights give integrability of the slope and curvature coefficients,
while the warp coefficient is integrable after multiplication by `x * (1 - x)`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter
open scoped ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The coefficient of the warp variation, evaluated on the weak derivative graph. -/
def weakCurvatureWarpCoefficient (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  weakMeridionalOperator K r p z x ^ 2 +
    2 * warp K x * weakMeridionalOperator K r p z x * z x -
    K x * warpSlope K x * r x * p x + K x ^ 2 * r x ^ 2

/-- The coefficient of the slope variation, evaluated on the weak derivative graph. -/
def weakCurvatureSlopeCoefficient (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  4 * warp K x * weakMeridionalOperator K r p z x * p x -
    K x * r x * (warp K x * p x + warpSlope K x * r x)

/-- The direct curvature coefficient, evaluated on the weak derivative graph. -/
def weakCurvatureCoefficient (K r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * warp K x * weakMeridionalOperator K r p z x * r x -
    warpSlope K x * r x * (warp K x * p x + warpSlope K x * r x / 2) +
    2 * K x * warp K x * r x ^ 2

/-- Ordinary derivatives recover the original warp coefficient exactly. -/
@[simp]
theorem weakCurvatureWarpCoefficient_deriv (K r : ℝ → ℝ) :
    weakCurvatureWarpCoefficient K r (deriv r) (deriv (deriv r)) =
      curvatureWarpCoefficient K r := rfl

/-- Ordinary derivatives recover the original slope coefficient exactly. -/
@[simp]
theorem weakCurvatureSlopeCoefficient_deriv (K r : ℝ → ℝ) :
    weakCurvatureSlopeCoefficient K r (deriv r) (deriv (deriv r)) =
      curvatureSlopeCoefficient K r := rfl

/-- Ordinary derivatives recover the original direct curvature coefficient exactly. -/
@[simp]
theorem weakCurvatureCoefficient_deriv (K r : ℝ → ℝ) :
    weakCurvatureCoefficient K r (deriv r) (deriv (deriv r)) =
      curvatureCoefficient K r := rfl

private theorem memLp_mul_of_ae_abs_coeff_le {μ : Measure ℝ}
    {a b v : ℝ → ℝ} {D : ℝ}
    (hav : AEStronglyMeasurable (fun x => a x * v x) μ)
    (hbv : MemLp (fun x => b x * v x) 2 μ)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ D * |b x|) :
    MemLp (fun x => a x * v x) 2 μ := by
  apply hbv.of_le_mul (c := D) hav
  filter_upwards [hab] with x hx
  simpa only [Real.norm_eq_abs, abs_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (v x))

private theorem integrable_mul_of_ae_abs_coeff_le {μ : Measure ℝ}
    {a b v : ℝ → ℝ} {D : ℝ}
    (hav : AEStronglyMeasurable (fun x => a x * v x) μ)
    (hbv : Integrable (fun x => b x * v x) μ)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ D * |b x|) :
    Integrable (fun x => a x * v x) μ := by
  apply (hbv.norm.const_mul D).mono' hav
  filter_upwards [hab] with x hx
  simpa only [Real.norm_eq_abs, abs_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (v x))

/-- The actual weak curvature coefficients have the integrability dictated by
parabolic graph regularity: the warp coefficient carries one parabolic weight,
whereas the slope and direct curvature coefficients are integrable themselves. -/
theorem IsRecoverableAreaCompetitor.curvature_coefficients_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    AEStronglyMeasurable (weakCurvatureWarpCoefficient K r p z) areaμ ∧
    Integrable (fun x => x * (1 - x) * weakCurvatureWarpCoefficient K r p z x) areaμ ∧
    Integrable (weakCurvatureSlopeCoefficient K r p z) areaμ ∧
    Integrable (weakCurvatureCoefficient K r p z) areaμ := by
  let w : ℝ → ℝ := fun x => x * (1 - x)
  let f : ℝ → ℝ := warp K
  let b : ℝ → ℝ := warpSlope K
  let q : ℝ → ℝ := weakMeridionalOperator K r p z
  have hgraph := h.2.1
  have hgeometry := h.geometry_bounds hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hhi : 0 ≤ 2 * C := by positivity
  have hwcont : Continuous w := by dsimp [w]; fun_prop
  have hwm : AEStronglyMeasurable w areaμ := hwcont.aestronglyMeasurable
  have hsw : AEStronglyMeasurable (fun x => Real.sqrt (w x)) areaμ :=
    hwcont.sqrt.aestronglyMeasurable
  have hf : AEStronglyMeasurable f areaμ :=
    ((hgeometry.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
  have hb : AEStronglyMeasurable b areaμ :=
    ((hgeometry.2.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
  have hK : AEStronglyMeasurable K areaμ := h.1.aestronglyMeasurable
  have hr : AEStronglyMeasurable r areaμ := hgraph.memLp.aestronglyMeasurable
  have hp : AEStronglyMeasurable p areaμ :=
    hgraph.weakDeriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hz : AEStronglyMeasurable z areaμ :=
    hgraph.weakDeriv_deriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hq : AEStronglyMeasurable q areaμ :=
    ((hf.mul hz).add ((aestronglyMeasurable_const.mul hb).mul hp)).sub (hK.mul hr)
  have hw : ∀ᵐ x ∂areaμ, 0 ≤ w x ∧ w x ≤ 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    refine ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), ?_⟩
    dsimp only [w]
    nlinarith only [hx.2, sq_nonneg x]
  have hfbox : ∀ᵐ x ∂areaμ, 0 ≤ f x ∧ f x ≤ (2 * C) * w x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hfx := hgeometry.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    have hwx : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
    refine ⟨?_, ?_⟩
    · have hlo : 0 ≤ (2 / C) * (x * (1 - x)) := mul_nonneg (by positivity) hwx
      exact hlo.trans (by simpa only [mul_assoc] using hfx.1)
    · simpa only [f, w, mul_assoc] using hfx.2.1
  have hab : ∀ᵐ x ∂areaμ, |b x| ≤ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    exact (hgeometry.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have haK : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [hgeometry.2.2.2.2] with x hx
    have hKnonneg : 0 ≤ K x := (by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1
    simpa only [abs_of_nonneg hKnonneg] using hx.2
  have haw : ∀ᵐ x ∂areaμ, |w x| ≤ 1 := by
    filter_upwards [hw] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hasw : ∀ᵐ x ∂areaμ, |Real.sqrt (w x)| ≤ 1 := by
    filter_upwards [hw] with x hx
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.2
  have hafw : ∀ᵐ x ∂areaμ, |f x| ≤ (2 * C) * |w x| := by
    filter_upwards [hfbox, hw] with x hx hwx
    simpa only [abs_of_nonneg hx.1, abs_of_nonneg hwx.1] using hx.2
  have haf : ∀ᵐ x ∂areaμ, |f x| ≤ 2 * C := by
    filter_upwards [hfbox, hw] with x hx hwx
    rw [abs_of_nonneg hx.1]
    exact hx.2.trans (mul_le_of_le_one_right hhi hwx.2)
  have hbnorm : ∀ᵐ x ∂areaμ, ‖b x‖ ≤ 2 := by
    simpa only [Real.norm_eq_abs] using hab
  have hKnorm : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    simpa only [Real.norm_eq_abs] using haK
  have hwnorm : ∀ᵐ x ∂areaμ, ‖w x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using haw
  have hfnorm : ∀ᵐ x ∂areaμ, ‖f x‖ ≤ 2 * C := by
    simpa only [Real.norm_eq_abs] using haf
  have hZ : MemLp (fun x => (Real.sqrt (w x) * f x) * z x) 2 areaμ := by
    apply memLp_mul_of_ae_abs_coeff_le (D := 2 * C)
      ((hsw.mul hf).mul hz) hgraph.memLp_weighted_secondDeriv
    filter_upwards [hfbox, hw] with x hx hwx
    change |Real.sqrt (w x) * f x| ≤ (2 * C) * |w x * Real.sqrt (w x)|
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx.1),
      abs_of_nonneg (mul_nonneg hwx.1 (Real.sqrt_nonneg _))]
    calc
      Real.sqrt (w x) * f x ≤ Real.sqrt (w x) * ((2 * C) * w x) :=
        mul_le_mul_of_nonneg_left hx.2 (Real.sqrt_nonneg _)
      _ = (2 * C) * (w x * Real.sqrt (w x)) := by ring
  have hP : MemLp (fun x => Real.sqrt (w x) * p x) 2 areaμ :=
    hgraph.memLp_weighted_deriv
  have hS : MemLp (fun x => Real.sqrt (w x) * r x) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hsw hasw hgraph.memLp
  have hKR : MemLp (fun x => K x * r x) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hK haK hgraph.memLp
  have hBP : MemLp (fun x => b x * (Real.sqrt (w x) * p x)) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hb hab hP
  have hSKR : MemLp (fun x => Real.sqrt (w x) * (K x * r x)) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hsw hasw hKR
  have hQ : MemLp (fun x => Real.sqrt (w x) * q x) 2 areaμ := by
    apply ((hZ.add (hBP.const_mul 2)).sub hSKR).ae_eq
    filter_upwards [] with x
    change (Real.sqrt (w x) * f x) * z x +
        2 * (b x * (Real.sqrt (w x) * p x)) -
        Real.sqrt (w x) * (K x * r x) =
      Real.sqrt (w x) * (f x * z x + 2 * b x * p x - K x * r x)
    ring
  have hWQQ : Integrable (fun x => w x * q x ^ 2) areaμ := by
    apply hQ.integrable_sq.congr
    filter_upwards [hw] with x hx
    rw [mul_pow, Real.sq_sqrt hx.1]
  have hWFQZ : Integrable (fun x => w x * f x * q x * z x) areaμ := by
    apply (hQ.integrable_mul hZ).congr
    filter_upwards [hw] with x hx
    calc
      (Real.sqrt (w x) * q x) * ((Real.sqrt (w x) * f x) * z x) =
          Real.sqrt (w x) ^ 2 * f x * q x * z x := by ring
      _ = w x * f x * q x * z x := by rw [Real.sq_sqrt hx.1]
  have hWRP : Integrable (fun x => w x * (r x * p x)) areaμ := by
    apply (hS.integrable_mul hP).congr
    filter_upwards [hw] with x hx
    calc
      (Real.sqrt (w x) * r x) * (Real.sqrt (w x) * p x) =
          Real.sqrt (w x) ^ 2 * (r x * p x) := by ring
      _ = w x * (r x * p x) := by rw [Real.sq_sqrt hx.1]
  have hWQP : Integrable (fun x => w x * (q x * p x)) areaμ := by
    apply (hQ.integrable_mul hP).congr
    filter_upwards [hw] with x hx
    calc
      (Real.sqrt (w x) * q x) * (Real.sqrt (w x) * p x) =
          Real.sqrt (w x) ^ 2 * (q x * p x) := by ring
      _ = w x * (q x * p x) := by rw [Real.sq_sqrt hx.1]
  have hWQR : Integrable (fun x => w x * (q x * r x)) areaμ := by
    apply (hQ.integrable_mul hS).congr
    filter_upwards [hw] with x hx
    calc
      (Real.sqrt (w x) * q x) * (Real.sqrt (w x) * r x) =
          Real.sqrt (w x) ^ 2 * (q x * r x) := by ring
      _ = w x * (q x * r x) := by rw [Real.sq_sqrt hx.1]
  have hFQP : Integrable (fun x => f x * (q x * p x)) areaμ :=
    integrable_mul_of_ae_abs_coeff_le (hf.mul (hq.mul hp)) hWQP hafw
  have hFRP : Integrable (fun x => f x * (r x * p x)) areaμ :=
    integrable_mul_of_ae_abs_coeff_le (hf.mul (hr.mul hp)) hWRP hafw
  have hFQR : Integrable (fun x => f x * (q x * r x)) areaμ :=
    integrable_mul_of_ae_abs_coeff_le (hf.mul (hq.mul hr)) hWQR hafw
  have hKBRP : Integrable (fun x => K x * (b x * (w x * (r x * p x)))) areaμ :=
    (hWRP.bdd_mul hb hbnorm).bdd_mul hK hKnorm
  have hWKR2 : Integrable (fun x => w x * (K x * r x) ^ 2) areaμ :=
    hKR.integrable_sq.bdd_mul hwm hwnorm
  have hKFRP : Integrable (fun x => K x * (f x * (r x * p x))) areaμ :=
    hFRP.bdd_mul hK hKnorm
  have hKBR2 : Integrable (fun x => K x * (b x * r x ^ 2)) areaμ :=
    (hgraph.integrable_sq.bdd_mul hb hbnorm).bdd_mul hK hKnorm
  have hBFRP : Integrable (fun x => b x * (f x * (r x * p x))) areaμ :=
    hFRP.bdd_mul hb hbnorm
  have hBBR2 : Integrable (fun x => b x * (b x * r x ^ 2)) areaμ :=
    (hgraph.integrable_sq.bdd_mul hb hbnorm).bdd_mul hb hbnorm
  have hKFR2 : Integrable (fun x => K x * (f x * r x ^ 2)) areaμ :=
    (hgraph.integrable_sq.bdd_mul hf hfnorm).bdd_mul hK hKnorm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((hq.pow 2).add
      (((aestronglyMeasurable_const.mul hf).mul hq).mul hz)).sub
      (((hK.mul hb).mul hr).mul hp)).add ((hK.pow 2).mul (hr.pow 2))
  · apply (((hWQQ.add (hWFQZ.const_mul 2)).sub hKBRP).add hWKR2).congr
    filter_upwards [] with x
    change w x * q x ^ 2 + 2 * (w x * f x * q x * z x) -
        K x * (b x * (w x * (r x * p x))) + w x * (K x * r x) ^ 2 =
      w x * (q x ^ 2 + 2 * f x * q x * z x -
        K x * b x * r x * p x + K x ^ 2 * r x ^ 2)
    ring
  · apply ((hFQP.const_mul 4).sub (hKFRP.add hKBR2)).congr
    filter_upwards [] with x
    change 4 * (f x * (q x * p x)) -
        (K x * (f x * (r x * p x)) + K x * (b x * r x ^ 2)) =
      4 * f x * q x * p x - K x * r x * (f x * p x + b x * r x)
    ring
  · apply (((hFQR.const_mul (-2)).sub
      (hBFRP.add (hBBR2.const_mul (1 / 2 : ℝ)))).add (hKFR2.const_mul 2)).congr
    filter_upwards [] with x
    change -2 * (f x * (q x * r x)) -
        (b x * (f x * (r x * p x)) + (1 / 2 : ℝ) * (b x * (b x * r x ^ 2))) +
        2 * (K x * (f x * r x ^ 2)) =
      -2 * f x * q x * r x - b x * r x * (f x * p x + b x * r x / 2) +
        2 * K x * f x * r x ^ 2
    ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
