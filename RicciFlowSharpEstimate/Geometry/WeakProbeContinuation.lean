/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.AbsolutelyContinuousUniqueness
import RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem

/-! # Interior continuation of the signed minimizing probe -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem four_energy_bound {r p q P dr dp dq dP B : ℝ} (hB : 0 ≤ B)
    (hr : |dr| ≤ B * (|r| + |p| + |q| + |P|))
    (hp : |dp| ≤ B * (|r| + |p| + |q| + |P|))
    (hq : |dq| ≤ B * (|r| + |p| + |q| + |P|))
    (hP : |dP| ≤ B * (|r| + |p| + |q| + |P|)) :
    |2 * r * dr + 2 * p * dp + 2 * q * dq + 2 * P * dP| ≤
      (8 * B) * (r ^ 2 + p ^ 2 + q ^ 2 + P ^ 2) := by
  let S := |r| + |p| + |q| + |P|
  have hS : S ^ 2 ≤ 4 * (r ^ 2 + p ^ 2 + q ^ 2 + P ^ 2) := by
    dsimp [S]
    nlinarith [sq_nonneg (|r| - |p|), sq_nonneg (|r| - |q|),
      sq_nonneg (|r| - |P|), sq_nonneg (|p| - |q|),
      sq_nonneg (|p| - |P|), sq_nonneg (|q| - |P|),
      sq_abs r, sq_abs p, sq_abs q, sq_abs P]
  calc
    _ ≤ |2 * r * dr| + |2 * p * dp| + |2 * q * dq| + |2 * P * dP| :=
      by linarith only [abs_add_le (2*r*dr+2*p*dp) (2*q*dq),
        abs_add_le (2*r*dr) (2*p*dp), abs_add_le (2*r*dr+2*p*dp+2*q*dq) (2*P*dP)]
    _ = 2 * |r| * |dr| + 2 * |p| * |dp| + 2 * |q| * |dq| + 2 * |P| * |dP| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * |r| * (B * S) + 2 * |p| * (B * S) +
        2 * |q| * (B * S) + 2 * |P| * (B * S) := by gcongr
    _ = 2 * B * S ^ 2 := by dsimp [S]; ring
    _ ≤ 2 * B * (4 * (r ^ 2 + p ^ 2 + q ^ 2 + P ^ 2)) := by gcongr
    _ = _ := by ring

private theorem four_state_zero {r p q P : ℝ → ℝ} {a b c B : ℝ}
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hP : AbsolutelyContinuousOnInterval P a b)
    (hB : 0 ≤ B)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc a b →
      |deriv r x| ≤ B * (|r x| + |p x| + |q x| + |P x|) ∧
      |deriv p x| ≤ B * (|r x| + |p x| + |q x| + |P x|) ∧
      |deriv q x| ≤ B * (|r x| + |p x| + |q x| + |P x|) ∧
      |deriv P x| ≤ B * (|r x| + |p x| + |q x| + |P x|))
    (hc : c ∈ uIcc a b) (hz : r c = 0 ∧ p c = 0 ∧ q c = 0 ∧ P c = 0) :
    ∀ x ∈ uIcc a b, r x = 0 ∧ p x = 0 ∧ q x = 0 ∧ P x = 0 := by
  let E := fun x => r x ^ 2 + p x ^ 2 + q x ^ 2 + P x ^ 2
  have hE : AbsolutelyContinuousOnInterval E a b := by
    simpa only [E, pow_two] using
      (((hr.fun_mul hr).fun_add (hp.fun_mul hp)).fun_add (hq.fun_mul hq)).fun_add (hP.fun_mul hP)
  have hn (x : ℝ) : 0 ≤ E x := by dsimp [E]; positivity
  have hED : ∀ᵐ x ∂volume, x ∈ uIcc a b → |deriv E x| ≤ (8 * B) * E x := by
    filter_upwards [hd, hr.ae_differentiableAt, hp.ae_differentiableAt,
      hq.ae_differentiableAt, hP.ae_differentiableAt] with x hx hrx hpx hqx hPx hxI
    have he := ((((hrx hxI).hasDerivAt.pow 2).add ((hpx hxI).hasDerivAt.pow 2)).add
      ((hqx hxI).hasDerivAt.pow 2)).add ((hPx hxI).hasDerivAt.pow 2)
    have heq : deriv E x = 2 * r x * deriv r x + 2 * p x * deriv p x +
        2 * q x * deriv q x + 2 * P x * deriv P x := by
      simpa only [E, Pi.add_def, Pi.pow_def, Nat.cast_ofNat, Nat.reduceSub, pow_one] using he.deriv
    rw [heq]
    exact four_energy_bound hB (hx hxI).1 (hx hxI).2.1 (hx hxI).2.2.1 (hx hxI).2.2.2
  have hEz : E c = 0 := by simp [E, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  have hzE := Analysis.AbsolutelyContinuousOnInterval.eq_zero_of_abs_deriv_le
    hE (fun x _ => hn x) hED hc hEz
  intro x hx
  have he : r x ^ 2 + p x ^ 2 + q x ^ 2 + P x ^ 2 = 0 := hzE x hx
  have hr0 : r x ^ 2 = 0 := by
    nlinarith only [he, sq_nonneg (p x), sq_nonneg (q x), sq_nonneg (P x)]
  have hp0 : p x ^ 2 = 0 := by
    nlinarith only [he, sq_nonneg (r x), sq_nonneg (q x), sq_nonneg (P x)]
  have hq0 : q x ^ 2 = 0 := by
    nlinarith only [he, sq_nonneg (r x), sq_nonneg (p x), sq_nonneg (P x)]
  have hP0 : P x ^ 2 = 0 := by
    nlinarith only [he, sq_nonneg (r x), sq_nonneg (p x), sq_nonneg (q x)]
  exact ⟨sq_eq_zero_iff.mp hr0, sq_eq_zero_iff.mp hp0, sq_eq_zero_iff.mp hq0, sq_eq_zero_iff.mp hP0⟩

private theorem physical_rates_bound {f b K lam r p q P M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 ≤ k) (hf : |f| ≤ k) (hb : |b| ≤ 2)
    (hK : |K| ≤ k) (hi : |f⁻¹| ≤ M) :
    let S := |r| + |p| + |q| + |P|
    let B := 1 + (1 + 4 + k) * M + (1 + k * k) * M ^ 2 +
      (k * k + k * k + (k ^ 2 * k + 2 * k) + |lam| * k)
    |p| ≤ B * S ∧
      |(q - 2 * b * p + K * r) / f| ≤ B * S ∧
      |(P - K * b * f * r / 2) / f ^ 2| ≤ B * S ∧
      |f * K * q + K * b * f * p / 2 -
        (K ^ 2 * f - K * b ^ 2 / 2) * r + lam * f * r| ≤ B * S := by
  dsimp only
  let S := |r| + |p| + |q| + |P|
  let B1 := (1 + 4 + k) * M
  let B2 := (1 + k * k) * M ^ 2
  let B3 := k * k + k * k + (k ^ 2 * k + 2 * k) + |lam| * k
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSr : |r| ≤ S := by dsimp [S]; linarith [abs_nonneg p, abs_nonneg q, abs_nonneg P]
  have hSp : |p| ≤ S := by dsimp [S]; linarith [abs_nonneg r, abs_nonneg q, abs_nonneg P]
  have hSq : |q| ≤ S := by dsimp [S]; linarith [abs_nonneg r, abs_nonneg p, abs_nonneg P]
  have hSP : |P| ≤ S := by dsimp [S]; linarith [abs_nonneg r, abs_nonneg p, abs_nonneg q]
  have h1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have h2 : 0 ≤ B2 := by dsimp [B2]; positivity
  have h3 : 0 ≤ B3 := by dsimp [B3]; positivity
  have hdp : |(q - 2 * b * p + K * r) / f| ≤ B1 * S := by
    calc
      _ = |q - 2 * b * p + K * r| * |f⁻¹| := by rw [div_eq_mul_inv, abs_mul]
      _ ≤ (|q| + 2 * |b| * |p| + |K| * |r|) * |f⁻¹| := by
        gcongr
        have hsub := abs_sub q (2 * b * p)
        have hadd := abs_add_le (q - 2 * b * p) (K * r)
        norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsub hadd
        linarith only [hsub, hadd]
      _ ≤ (S + 2 * 2 * S + k * S) * M := by gcongr
      _ = B1 * S := by dsimp [B1]; ring
  have hdq : |(P - K * b * f * r / 2) / f ^ 2| ≤ B2 * S := by
    calc
      _ = |P - K * b * f * r / 2| * |f⁻¹| ^ 2 := by
        rw [div_eq_mul_inv, abs_mul, ← inv_pow, abs_pow]
      _ ≤ (|P| + |K| * |b| * |f| * |r| / 2) * |f⁻¹| ^ 2 := by
        gcongr
        simpa only [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          using abs_sub P (K * b * f * r / 2)
      _ ≤ (S + k * 2 * k * S / 2) * M ^ 2 := by gcongr
      _ = B2 * S := by dsimp [B2]; ring
  have hdP : |f * K * q + K * b * f * p / 2 -
      (K ^ 2 * f - K * b ^ 2 / 2) * r + lam * f * r| ≤ B3 * S := by
    calc
      _ ≤ |f * K * q| + |K * b * f * p / 2| +
          |(K ^ 2 * f - K * b ^ 2 / 2) * r| + |lam * f * r| := by
        linarith only [abs_add_le (f*K*q) (K*b*f*p/2),
          abs_sub (f*K*q+K*b*f*p/2) ((K^2*f-K*b^2/2)*r),
          abs_add_le (f*K*q+K*b*f*p/2-(K^2*f-K*b^2/2)*r) (lam*f*r)]
      _ ≤ |f| * |K| * |q| + |K| * |b| * |f| * |p| / 2 +
          (|K| ^ 2 * |f| + |K| * |b| ^ 2 / 2) * |r| + |lam| * |f| * |r| := by
        simp only [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        calc
          _ ≤ |K ^ 2 * f| + |K * b ^ 2 / 2| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_pow, abs_div, abs_mul, abs_pow]; norm_num
      _ ≤ k * k * S + k * 2 * k * S / 2 +
          (k ^ 2 * k + k * 2 ^ 2 / 2) * S + |lam| * k * S := by gcongr
      _ = B3 * S := by dsimp [B3]; ring
  change |p| ≤ (1 + B1 + B2 + B3) * S ∧ _ ∧ _ ∧ _
  refine ⟨hSp.trans ?_, hdp.trans ?_, hdq.trans ?_, hdP.trans ?_⟩ <;>
    nlinarith [mul_nonneg h1 hS, mul_nonneg h2 hS, mul_nonneg h3 hS]

/-- The genuine signed minimizing state never vanishes in all four
coordinates at an interior point. This uses its actual mass and weak equations,
with no sign condition on the operator or derivative of the curvature. -/
theorem IsRecoverableAreaCompetitor.probe_state_ne_zero_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let P := weakProbeEulerFlux K r p z lam
    let q := fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2
    ∀ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0 ∨ p x ≠ 0 ∨ q x ≠ 0 ∨ P x ≠ 0 := by
  let lam := weakMeridionalAction K r p z
  let P := weakProbeEulerFlux K r p z lam
  let q := fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2
  obtain ⟨hrD, hrC, _, _, hAC, hD⟩ := h.probe_first_order_system_of_minimum hC hr hp hmin
  have hPAC : AbsolutelyContinuousOnInterval P 0 1 :=
    (h.probe_euler_flux_of_minimum hC hmin).2.1
  have hg := h.geometry_bounds hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  change ∀ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0 ∨ p x ≠ 0 ∨ q x ≠ 0 ∨ P x ≠ 0
  intro c hc
  by_contra hn
  push Not at hn
  have hrzero (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : r x = 0 := by
    have hsub : uIcc c x ⊆ Ioo (0 : ℝ) 1 := by
      intro t ht
      rcases mem_uIcc.mp ht with ht | ht
      · exact ⟨hc.1.trans_le ht.1, ht.2.trans_lt hx.2⟩
      · exact ⟨hx.1.trans_le ht.1, ht.2.trans_lt hc.2⟩
    have hfinv : ContinuousOn (fun t => (warp K t)⁻¹) (uIcc c x) :=
      (hg.1.mono (hsub.trans Ioo_subset_Icc_self)).inv₀
        (fun t ht => (hfpos t (hsub ht)).ne')
    obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hfinv
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (left_mem_uIcc))
    let k := 2 * C
    let B := 1 + (1 + 4 + k) * M + (1 + k * k) * M ^ 2 +
      (k * k + k * k + (k ^ 2 * k + 2 * k) + |lam| * k)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hder : ∀ᵐ t ∂volume, t ∈ uIcc c x →
        |deriv r t| ≤ B * (|r t| + |p t| + |q t| + |P t|) ∧
        |deriv p t| ≤ B * (|r t| + |p t| + |q t| + |P t|) ∧
        |deriv q t| ≤ B * (|r t| + |p t| + |q t| + |P t|) ∧
        |deriv P t| ≤ B * (|r t| + |p t| + |q t| + |P t|) := by
      have hdae := (ae_restrict_iff' measurableSet_Ioo).mp hD
      have hkae := (ae_restrict_iff' measurableSet_Ioo).mp hg.2.2.2.2
      filter_upwards [hdae, hkae] with t htD htK ht
      have htI := hsub ht
      have hK0 : 0 ≤ K t := (by positivity : (0 : ℝ) ≤ 2 / C).trans (htK htI).1
      have hf : |warp K t| ≤ k := by
        rw [abs_of_pos (hfpos t htI)]
        have hbound := (hg.2.2.1 t ⟨htI.1.le, htI.2.le⟩).2.1
        have hw : t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg t]
        calc
          _ ≤ k * (t * (1 - t)) := by simpa only [k, mul_assoc] using hbound
          _ ≤ k * 1 := mul_le_mul_of_nonneg_left hw hk
          _ = k := mul_one k
      have hbound := physical_rates_bound hM0 hk hf
        (hg.2.2.1 t ⟨htI.1.le, htI.2.le⟩).2.2
        (show |K t| ≤ k by simpa only [abs_of_nonneg hK0] using (htK htI).2)
        (show |(warp K t)⁻¹| ≤ M by simpa only [Real.norm_eq_abs] using hM t ht)
        (lam := lam) (r := r t) (p := p t) (q := q t) (P := P t)
      rw [(hrD t htI).deriv, (htD htI).1.deriv, (htD htI).2.1.deriv,
        (htD htI).2.2.deriv]
      exact hbound
    have hPcx : AbsolutelyContinuousOnInterval P c x := hPAC.mono (by
      simpa only [uIcc_of_le zero_le_one] using hsub.trans Ioo_subset_Icc_self)
    exact (four_state_zero (hrC.mono hsub).absolutelyContinuousOnInterval
      (hAC c hc x hx).1 (hAC c hc x hx).2 hPcx hB hder
      left_mem_uIcc hn x right_mem_uIcc).1
  have hm : probeMass K r = 0 := by
    unfold probeMass
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [hrzero x hx, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, Pi.zero_apply]
  have hmass : probeMass K r = 1 := h.2.2.2.2.2.1
  linarith

end RicciFlowSharpEstimate.Geometry.AreaProfile
