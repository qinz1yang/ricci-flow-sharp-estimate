/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.IntegralAverageRemainder
import RicciFlowSharpEstimate.Analysis.ClampedIteratedAverage

/-! # Selecting a clamped pole limit from its genuine derivative feedback -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

private theorem zero_mul_bounded {α : Type*} {l : Filter α} {u v : α → ℝ} {B : ℝ}
    (hu : Tendsto u l (𝓝 0)) (hv : ∀ᶠ x in l, |v x| ≤ B) :
    Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hv] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simpa only [norm_zero, zero_mul, Real.norm_eq_abs] using hu.norm.mul_const B

/-- A complete first derivative with bounded curvature-average feedback
selects the actual clamped quotient limit. Neither average nor curvature
is assumed to have an endpoint limit. -/
theorem tendsto_clamp_of_derivative_average
    {H D K : ℝ → ℝ} {b lo hi δ γ L : ℝ}
    (hb : 0 < b) (hlohi : lo ≤ hi) (hγ : 0 ≤ γ) (hγδ : γ < δ)
    (hK : IntegrableOn K (Ioo 0 b))
    (hbox : ∀ x ∈ Ioo (0 : ℝ) b, lo ≤ K x ∧ K x ≤ hi)
    (hH : DifferentiableOn ℝ H (Ioo 0 b))
    (hH0 : Tendsto H (𝓝[>] 0) (𝓝 0))
    (hderiv : Tendsto (fun x => deriv H x - γ * (⨍ t in (0 : ℝ)..x, K t))
      (𝓝[>] 0) (𝓝 L))
    (hD : Tendsto (fun x => D x / x) (𝓝[>] 0) (𝓝 δ))
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = max lo (min hi (-H x / D x))) :
    Tendsto K (𝓝[>] 0) (𝓝 (max lo (min hi (-L / (δ + γ))))) := by
  have hδ : 0 < δ := hγ.trans_lt hγδ
  let B := |lo| + |hi|
  let M := fun x => ⨍ s in (0 : ℝ)..x, ⨍ t in (0 : ℝ)..s, K t
  have hKB : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), |K t| ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htB := hbox t ht
    apply abs_le.mpr
    dsimp only [B]
    constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
  have hInner := integrableOn_interval_average_of_ae_bound hK hKB
  have hGI : IntegrableOn (fun x => γ * (⨍ t in (0 : ℝ)..x, K t)) (Ioo (0 : ℝ) b) :=
    hInner.const_mul γ
  have hnum : Tendsto (fun x => H x / x - γ * M x) (𝓝[>] 0) (𝓝 L) := by
    apply (tendsto_div_sub_interval_average_of_deriv hb hH hGI hH0 hderiv).congr'
    filter_upwards [] with x
    rw [interval_average_eq_div, intervalIntegral.integral_const_mul]
    dsimp only [M]
    rw [interval_average_eq_div]
    ring
  have hMB (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : |M x| ≤ B := by
    have hs : Ioo (0 : ℝ) x ⊆ Ioo (0 : ℝ) b :=
      fun _ ht => ⟨ht.1, ht.2.trans hx.2⟩
    have hbs := hKB.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
    simpa only [sub_zero] using abs_iterated_interval_average_sub_le_of_ae_bound
      (c := 0) hx.1 (hK.mono_set hs) (by simpa only [sub_zero] using hbs)
  let d := fun x => D x / x
  let S := fun x => H x / x - γ * M x
  let A := -L / δ
  let ρ := γ / δ
  let e := fun x => -H x / D x - (A - ρ * M x)
  have hρ0 : 0 ≤ ρ := div_nonneg hγ hδ.le
  have hρ1 : ρ < 1 := (div_lt_one hδ).mpr hγδ
  have hldom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) b := Ioo_mem_nhdsGT hb
  have hU : Tendsto (fun x => -(S x / d x) + L / δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [S, d, Pi.div_apply, neg_add_cancel] using
      (hnum.div hD hδ.ne').neg.add_const (L / δ)
  have hCoeff : Tendsto (fun x => γ / δ - γ / d x) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun x => γ / d x) (𝓝[>] 0) (𝓝 (γ / δ)) :=
      tendsto_const_nhds.div hD hδ.ne'
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => γ / δ)
        (𝓝[>] 0) (𝓝 (γ / δ))).sub hh
  have hV := zero_mul_bounded hCoeff (hldom.mono fun x hx => hMB x hx)
  have hdpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < d x := hD.eventually (lt_mem_nhds hδ)
  have he : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    apply (show Tendsto (fun x => (-(S x / d x) + L / δ) +
      (γ / δ - γ / d x) * M x) (𝓝[>] 0) (𝓝 0) from
        by simpa only [add_zero] using hU.add hV).congr'
    filter_upwards [hldom, hdpos] with x hx hdx
    have hDx : D x ≠ 0 := by
      intro hz
      change 0 < D x / x at hdx
      simp only [hz, zero_div, lt_self_iff_false] at hdx
    dsimp only [e, S, d, A, ρ]
    field_simp [hδ.ne', hx.1.ne', hDx]
    ring
  have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      K x = max lo (min hi (A - ρ * M x + e x)) := by
    filter_upwards [hclip] with x hx
    have heq : A - ρ * M x + e x = -H x / D x := by
      dsimp only [e]
      ring
    rw [heq]
    exact hx
  have ht := tendsto_of_clamped_iterated_average hb hlohi hρ0 hρ1 hK hbox he hc
  have hfixed : A / (1 + ρ) = -L / (δ + γ) := by
    have hsum : δ + γ ≠ 0 := (add_pos_of_pos_of_nonneg hδ hγ).ne'
    dsimp only [A, ρ]
    field_simp [hδ.ne', hsum]
  rwa [hfixed] at ht

end RicciFlowSharpEstimate.Analysis
