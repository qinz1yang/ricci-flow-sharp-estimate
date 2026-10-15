/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SingularVolterraUniqueness
import RicciFlowSharpEstimate.Analysis.IntegrableDerivativeExtension
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Boundary uniqueness for a degenerate, coupled flux system -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

private theorem integrableOn_of_continuousOn_bound {u : ℝ → ℝ} {b N : ℝ}
    (hu : ContinuousOn u (Ioo (0 : ℝ) b))
    (hN : ∀ x ∈ Ioo (0 : ℝ) b, |u x| ≤ N) : IntegrableOn u (Ioo (0 : ℝ) b) := by
  apply (integrableOn_const (C := N)
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne).mono'
    (hu.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hN x hx

private theorem ac_abs_le_integral {u g : ℝ → ℝ} {b x : ℝ}
    (hb : 0 < b) (hx : x ∈ Ioo (0 : ℝ) b)
    (hu : AbsolutelyContinuousOnInterval u 0 b) (h0 : u 0 = 0)
    (hg : IntegrableOn g (Ioo (0 : ℝ) b))
    (hd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), |deriv u t| ≤ g t) :
    |u x| ≤ ∫ t in (0 : ℝ)..x, g t := by
  have hs : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hx.1.le, uIcc_of_le hb.le]
    exact Icc_subset_Icc le_rfl hx.2.le
  have hG : IntervalIntegrable g volume 0 x :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr hg).mono_set hs
  have hh := intervalIntegral.norm_integral_le_of_norm_le hx.1.le (f := deriv u)
    (g := g) (by
      filter_upwards [ae_imp_of_ae_restrict hd] with t ht htI
      simpa only [Real.norm_eq_abs] using ht ⟨htI.1, htI.2.trans_lt hx.2⟩) hG
  simpa only [Real.norm_eq_abs, (hu.mono hs).integral_deriv_eq_sub, h0, sub_zero] using hh

private theorem ae_hasDerivAt_of_local_ac {q : ℝ → ℝ} {b : ℝ}
    (hq : ∀ a ∈ Ioo (0 : ℝ) b, ∀ c ∈ Ioo (0 : ℝ) b,
      AbsolutelyContinuousOnInterval q a c) :
    ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b), HasDerivAt q (deriv q x) x := by
  have hdiff (a c : ℚ) : ∀ᵐ x ∂volume,
      (a : ℝ) ∈ Ioo (0 : ℝ) b → (c : ℝ) ∈ Ioo (0 : ℝ) b →
        x ∈ uIcc (a : ℝ) (c : ℝ) → DifferentiableAt ℝ q x := by
    by_cases ha : (a : ℝ) ∈ Ioo (0 : ℝ) b
    · by_cases hc : (c : ℝ) ∈ Ioo (0 : ℝ) b
      · filter_upwards [(hq a ha c hc).ae_differentiableAt] with x hx _ _ hxI
        exact hx hxI
      · filter_upwards [] with x _ hc'
        exact (hc hc').elim
    · filter_upwards [] with x ha'
      exact (ha ha').elim
  have hall : ∀ᵐ x ∂volume, ∀ a c : ℚ,
      (a : ℝ) ∈ Ioo (0 : ℝ) b → (c : ℝ) ∈ Ioo (0 : ℝ) b →
        x ∈ uIcc (a : ℝ) (c : ℝ) → DifferentiableAt ℝ q x :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun c => hdiff a c))
  filter_upwards [hall.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  obtain ⟨a, ha0, hax⟩ := exists_rat_btwn hxI.1
  obtain ⟨c, hxc, hcb⟩ := exists_rat_btwn hxI.2
  exact (hx a c ⟨ha0, hax.trans hxI.2⟩ ⟨hxI.1.trans hxc, hcb⟩
    (mem_uIcc_of_le hax.le hxc.le)).hasDerivAt

/-- Genuine derivative bounds for the coupled states imply boundary uniqueness.
The derivative flux controls p with the singular squared-coordinate weight;
no nonzero leading coefficient, pole derivative or auxiliary selector is assumed. -/
theorem exists_zero_interval_of_singular_flux_bounds
    {r p q P F : ℝ → ℝ} {b A B D : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hr : AbsolutelyContinuousOnInterval r 0 b) (hr0 : r 0 = 0)
    (hp : ContinuousOn p (Ioo (0 : ℝ) b)) (hq : ContinuousOn q (Ioo (0 : ℝ) b))
    (hrD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b), HasDerivAt r (p x) x)
    (hqlocal : ∀ a ∈ Ioo (0 : ℝ) b, ∀ c ∈ Ioo (0 : ℝ) b,
      AbsolutelyContinuousOnInterval q a c)
    (hq0 : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hP : AbsolutelyContinuousOnInterval P 0 b) (hP0 : P 0 = 0)
    (hF : AbsolutelyContinuousOnInterval F 0 b) (hF0 : F 0 = 0)
    (hbound : ∃ N : ℝ, 0 ≤ N ∧ ∀ x ∈ Ioo (0 : ℝ) b, |p x| ≤ N ∧ |q x| ≤ N)
    (hPD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      |deriv P x| ≤ A * x * (|q x| + |p x| + |r x| / x))
    (hQD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      |deriv q x| ≤ B * (|P x| / x ^ 2 + |r x| / x))
    (hFD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      |deriv F x| ≤ A * x * (|q x| + |r x|))
    (hFP : ∀ x ∈ Ioo (0 : ℝ) b, |p x| ≤ D * |F x| / x ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < b ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, r x = 0 ∧ p x = 0 ∧ q x = 0 ∧ P x = 0 := by
  let μ := volume.restrict (Ioo (0 : ℝ) b)
  obtain ⟨N, hN, hNb⟩ := hbound
  have hrC : ContinuousOn r (Ioo (0 : ℝ) b) :=
    hr.continuousOn.mono (by rw [uIcc_of_le hb.le]; exact Ioo_subset_Icc_self)
  have hpI := integrableOn_of_continuousOn_bound hp (fun x hx => (hNb x hx).1)
  have hrd : ∀ᵐ x ∂μ, |deriv r x| ≤ |p x| := by
    filter_upwards [hrD] with x hx
    rw [hx.deriv]
  have hrInt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) :
      |r x| ≤ ∫ t in (0 : ℝ)..x, |p t| := ac_abs_le_integral hb hx hr hr0 hpI.norm hrd
  have hrB (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : |r x| ≤ N * x := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := fun t => |p t|) (a := 0) (b := x) (C := N) (by
        filter_upwards [] with t ht
        have htI : t ∈ Ioo (0 : ℝ) b := by
          rw [uIoc_of_le hx.1.le] at ht
          exact ⟨ht.1, ht.2.trans_lt hx.2⟩
        simpa only [Real.norm_eq_abs, abs_abs] using (hNb t htI).1)
    exact (hrInt x hx).trans ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hx.1] using hh))
  have hrDiv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : |r x| / x ≤ N :=
    (div_le_iff₀ hx.1).mpr (hrB x hx)
  let E := fun x => |q x| + |p x| + |r x| / x
  have hE : ContinuousOn E (Ioo (0 : ℝ) b) :=
    (hq.abs.add hp.abs).add (hrC.abs.div continuousOn_id (fun _ hx => hx.1.ne'))
  have hEN (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : E x ≤ 3 * N := by
    dsimp only [E]
    linarith [(hNb x hx).1, (hNb x hx).2, hrDiv x hx]
  have hE0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : 0 ≤ E x := by
    dsimp only [E]
    exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (div_nonneg (abs_nonneg _) hx.1.le)
  have hPI : IntegrableOn (fun x => A * x * E x) (Ioo (0 : ℝ) b) := by
    apply integrableOn_of_continuousOn_bound (N := A * b * (3 * N))
      ((continuousOn_const.mul continuousOn_id).mul hE)
    intro x hx
    change |A * x * E x| ≤ A * b * (3 * N)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA hx.1.le) (hE0 x hx))]
    exact (mul_le_mul_of_nonneg_left (hEN x hx) (mul_nonneg hA hx.1.le)).trans
      (by gcongr; exact hx.2.le)
  have hPInt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) :
      |P x| ≤ A * ∫ t in (0 : ℝ)..x, t * E t := by
    simpa only [mul_assoc, intervalIntegral.integral_const_mul] using
      ac_abs_le_integral hb hx hP hP0 hPI hPD
  have hPB (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : |P x| ≤ A * (3 * N) * x ^ 2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := fun t => t * E t) (a := 0) (b := x) (C := x * (3 * N)) (by
        filter_upwards [] with t ht
        rw [uIoc_of_le hx.1.le] at ht
        have htI : t ∈ Ioo (0 : ℝ) b := ⟨ht.1, ht.2.trans_lt hx.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1.le (hE0 t htI))]
        exact (mul_le_mul_of_nonneg_left (hEN t htI) ht.1.le).trans
          (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
    have hi : (∫ t in (0 : ℝ)..x, t * E t) ≤ (x * (3 * N)) * x :=
      (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hx.1] using hh)
    exact (hPInt x hx).trans (by nlinarith only [mul_le_mul_of_nonneg_left hi hA])
  have hqIB : ∀ᵐ x ∂μ, ‖deriv q x‖ ≤ B * (A * (3 * N) + N) := by
    filter_upwards [hQD, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hPquot : |P x| / x ^ 2 ≤ A * (3 * N) :=
      (div_le_iff₀ (sq_pos_of_pos hxI.1)).mpr (hPB x hxI)
    rw [Real.norm_eq_abs]
    exact hx.trans (mul_le_mul_of_nonneg_left (add_le_add hPquot (hrDiv x hxI)) hB)
  have hqI : IntegrableOn (deriv q) (Ioo (0 : ℝ) b) :=
    (integrableOn_const (C := B * (A * (3 * N) + N))
      ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne).mono'
      (stronglyMeasurable_deriv q).aestronglyMeasurable hqIB
  obtain ⟨Q, hQAC, hQeq, hQL, _, _⟩ :=
    exists_boundary_extension_of_integrable_deriv hb hqlocal
      (ae_hasDerivAt_of_local_ac hqlocal) hqI
  have hQ0 : Q 0 = 0 := tendsto_nhds_unique hQL hq0
  have hQder : ∀ᵐ x ∂μ, deriv Q x = deriv q x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have he : Q =ᶠ[𝓝 x] q :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) b from isOpen_Ioo.mem_nhds hx).mono
        (fun _ hy => hQeq hy)
    exact he.deriv_eq
  have hQCI : ContinuousOn (fun x => |P x| / x ^ 2 + |r x| / x) (Ioo (0 : ℝ) b) :=
    (hP.continuousOn.mono (by rw [uIcc_of_le hb.le]; exact Ioo_subset_Icc_self) |>.abs.div
      (continuousOn_id.pow 2) (fun _ hx => pow_ne_zero 2 hx.1.ne')).add
        (hrC.abs.div continuousOn_id (fun _ hx => hx.1.ne'))
  have hQBI : IntegrableOn (fun x => B * (|P x| / x ^ 2 + |r x| / x))
      (Ioo (0 : ℝ) b) := by
    apply integrableOn_of_continuousOn_bound (N := B * (A * (3 * N) + N))
      (continuousOn_const.mul hQCI)
    intro x hx
    change |B * (|P x| / x ^ 2 + |r x| / x)| ≤ B * (A * (3 * N) + N)
    have hPQ := (div_le_iff₀ (sq_pos_of_pos hx.1)).mpr (hPB x hx)
    rw [abs_of_nonneg (mul_nonneg hB (add_nonneg
      (div_nonneg (abs_nonneg _) (sq_nonneg _)) (div_nonneg (abs_nonneg _) hx.1.le)))]
    exact mul_le_mul_of_nonneg_left (add_le_add hPQ (hrDiv x hx)) hB
  have hqInt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) :
      |q x| ≤ B * ∫ t in (0 : ℝ)..x, (|P t| / t ^ 2 + |r t| / t) := by
    rw [← hQeq hx]
    have hh := ac_abs_le_integral hb hx hQAC hQ0 hQBI (by
      filter_upwards [hQder, hQD] with t he ht
      simpa only [he] using ht)
    simpa only [intervalIntegral.integral_const_mul] using hh
  have hFI : IntegrableOn (fun x => A * x * (|q x| + |r x|)) (Ioo (0 : ℝ) b) := by
    apply integrableOn_of_continuousOn_bound (N := A * b * (N + N * b))
      ((continuousOn_const.mul continuousOn_id).mul (hq.abs.add hrC.abs))
    intro x hx
    change |A * x * (|q x| + |r x|)| ≤ A * b * (N + N * b)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA hx.1.le)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))]
    have hrN : |r x| ≤ N * b := (hrB x hx).trans (mul_le_mul_of_nonneg_left hx.2.le hN)
    exact (mul_le_mul_of_nonneg_left (add_le_add (hNb x hx).2 hrN)
      (mul_nonneg hA hx.1.le)).trans (by gcongr; exact hx.2.le)
  have hpInt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) :
      |p x| ≤ (D * A) / x ^ 2 * ∫ t in (0 : ℝ)..x, t * (|q t| + |r t|) := by
    have hh := ac_abs_le_integral hb hx hF hF0 hFI hFD
    simp only [mul_assoc, intervalIntegral.integral_const_mul] at hh
    exact (hFP x hx).trans (by
      have hh' := mul_le_mul_of_nonneg_left hh hD
      have hd := div_le_div_of_nonneg_right hh' (sq_nonneg x)
      simpa only [mul_div_assoc, mul_assoc, div_mul_eq_mul_div] using hd)
  let B' := B + D * A
  have hB' : 0 ≤ B' := by dsimp only [B']; positivity
  apply exists_eq_zero_of_singular_volterra_bounds hb hA hB' ⟨3 * N, hEN⟩ hrInt hPInt
  · intro x hx
    have hi : 0 ≤ ∫ t in (0 : ℝ)..x, (|P t| / t ^ 2 + |r t| / t) := by
      apply intervalIntegral.integral_nonneg hx.1.le
      intro t ht
      exact add_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _))
        (div_nonneg (abs_nonneg _) ht.1)
    exact (hqInt x hx).trans (mul_le_mul_of_nonneg_right
      (by dsimp only [B']; linarith [mul_nonneg hD hA]) hi)
  · intro x hx
    have hi : 0 ≤ ∫ t in (0 : ℝ)..x, t * (|q t| + |r t|) := by
      apply intervalIntegral.integral_nonneg hx.1.le
      intro t ht
      exact mul_nonneg ht.1 (add_nonneg (abs_nonneg _) (abs_nonneg _))
    exact (hpInt x hx).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by dsimp only [B']; linarith) (sq_nonneg x)) hi)

end RicciFlowSharpEstimate.Analysis
