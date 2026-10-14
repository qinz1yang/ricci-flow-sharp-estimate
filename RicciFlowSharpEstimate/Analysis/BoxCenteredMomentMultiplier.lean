/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A multiplier for the centered moment in a box

A constrained minimum of an integrable linear cost over a nondegenerate
almost-everywhere box has one scalar multiplier for the centered first moment.
The total integral is unconstrained. An explicit affine perturbation of the
box midpoint supplies qualification, including boxes with nonpositive endpoints.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem centered_box_integrable {J : ℝ → ℝ} {lo hi : ℝ}
    (hJ : AEStronglyMeasurable J areaμ)
    (hbox : ∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) :
    Integrable J areaμ := by
  refine (integrable_const (max |lo| |hi|)).mono' hJ ?_
  filter_upwards [hbox] with x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |lo| |hi|)).trans
      ((neg_abs_le lo).trans hx.1)
  · exact hx.2.trans ((le_abs_self hi).trans (le_max_right |lo| |hi|))

private theorem centered_weighted_box_integrable {W J : ℝ → ℝ} {lo hi : ℝ}
    (hW : Integrable W areaμ) (hJ : AEStronglyMeasurable J areaμ)
    (hbox : ∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) :
    Integrable (fun x => W x * J x) areaμ := by
  apply hW.mul_bdd hJ (c := max |lo| |hi|)
  filter_upwards [hbox] with x hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |lo| |hi|)).trans
      ((neg_abs_le lo).trans hx.1)
  · exact hx.2.trans ((le_abs_self hi).trans (le_max_right |lo| |hi|))

private theorem centered_moment_integrable {J : ℝ → ℝ}
    (hJ : Integrable J areaμ) :
    Integrable (fun x => (x - (1 / 2 : ℝ)) * J x) areaμ := by
  apply hJ.bdd_mul (continuous_id.sub continuous_const).aestronglyMeasurable
    (c := (1 / 2 : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  change |x - (1 / 2 : ℝ)| ≤ 1 / 2
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2]

private theorem centered_weighted_mix {w f g : ℝ → ℝ}
    (hf : Integrable (fun x => w x * f x) areaμ)
    (hg : Integrable (fun x => w x * g x) areaμ) (a b : ℝ) :
    (∫ x, w x * (a * f x + b * g x) ∂areaμ) =
      a * (∫ x, w x * f x ∂areaμ) + b * (∫ x, w x * g x ∂areaμ) := by
  calc
    _ = ∫ x, a * (w x * f x) + b * (w x * g x) ∂areaμ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [integral_add (hf.const_mul a) (hg.const_mul b),
        integral_const_mul, integral_const_mul]

private theorem centered_constant_moment (c : ℝ) :
    (∫ x, (x - (1 / 2 : ℝ)) * c ∂areaμ) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_mul_const]
  have hxi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hci : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hxi hci]
  norm_num [integral_id]

private theorem centered_square_moment :
    (∫ x, (x - (1 / 2 : ℝ)) * (x - (1 / 2 : ℝ)) ∂areaμ) = 1 / 12 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ x in (0 : ℝ)..1, (x ^ 2 - x) + (1 / 4 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = (∫ x in (0 : ℝ)..1, x ^ 2) - (∫ x in (0 : ℝ)..1, x) +
        (∫ _ in (0 : ℝ)..1, (1 / 4 : ℝ)) := by
      have hxi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
        continuous_id.intervalIntegrable 0 1
      have hx2i : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
        (continuous_id.pow 2).intervalIntegrable 0 1
      have hsubi : IntervalIntegrable (fun x : ℝ => x ^ 2 - x) volume 0 1 :=
        hx2i.sub hxi
      have hci : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume 0 1 :=
        continuous_const.intervalIntegrable 0 1
      rw [intervalIntegral.integral_add hsubi hci,
        intervalIntegral.integral_sub hx2i hxi]
    _ = 1 / 12 := by norm_num [integral_pow, integral_id]

private theorem centered_epigraph_separator
    (S : Set (ℝ × ℝ)) (hconv : Convex ℝ S)
    (hint : (interior S).Nonempty) (hzero : (0 : ℝ × ℝ) ∉ S)
    (hvertical : ((0, 1) : ℝ × ℝ) ∈ S) (δ : ℝ) (hδ : 0 < δ)
    (hqual : ∀ u : ℝ, |u| < δ → ∃ v : ℝ, (u, v) ∈ S) :
    ∃ t : ℝ, ∀ z ∈ S, t * z.1 ≤ z.2 := by
  obtain ⟨f, hfne, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hconv (fun h => hzero (interior_subset h)) hint
  let p : ℝ := f (1, 0)
  let r : ℝ := f (0, 1)
  have hformula (z : ℝ × ℝ) : f z = p * z.1 + r * z.2 := by
    have hz : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp only [p, r]
    ring
  have hnonpos (z : ℝ × ℝ) (hz : z ∈ S) :
      p * z.1 + r * z.2 ≤ 0 := by
    have hh := hsep z hz
    rw [map_zero, hformula] at hh
    exact hh
  have hrle : r ≤ 0 := by simpa using hnonpos _ hvertical
  have hr : r < 0 := by
    by_contra hn
    have hrzero : r = 0 := le_antisymm hrle (le_of_not_gt hn)
    have hh : |δ / 2| < δ := by rw [abs_of_pos (half_pos hδ)]; linarith
    have hhn : |-(δ / 2)| < δ := by simpa only [abs_neg] using hh
    obtain ⟨vp, hvp⟩ := hqual (δ / 2) hh
    obtain ⟨vn, hvn⟩ := hqual (-(δ / 2)) hhn
    have hp := hnonpos _ hvp
    have hn := hnonpos _ hvn
    simp only [hrzero, zero_mul, add_zero] at hp hn
    have hpδ : p * (δ / 2) = 0 := by nlinarith
    have hpzero : p = 0 := (mul_eq_zero.mp hpδ).resolve_right (half_pos hδ).ne'
    apply hfne
    apply DFunLike.ext
    intro z
    change f z = 0
    rw [hformula, hpzero, hrzero]
    ring
  refine ⟨-p / r, ?_⟩
  intro z hz
  have hdiv := div_nonneg_of_nonpos (hnonpos z hz) hr.le
  have heq : (p * z.1 + r * z.2) / r = z.2 - (-p / r) * z.1 := by
    field_simp [hr.ne]
    ring
  rw [heq] at hdiv
  linarith

/-- A minimum of an integrable linear cost over an a.e. box with zero centered
first moment admits one scalar multiplier on the entire box. No total-integral
constraint or positivity of the box endpoints is assumed. Qualification follows
from affine perturbations of the midpoint of the nondegenerate box. -/
theorem exists_box_centered_moment_multiplier
    (W K : ℝ → ℝ) (lo hi : ℝ) (hlohi : lo < hi)
    (hW : Integrable W areaμ)
    (hK : AEStronglyMeasurable K areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, lo ≤ K x ∧ K x ≤ hi)
    (hKm : (∫ x, (x - (1 / 2 : ℝ)) * K x ∂areaμ) = 0)
    (hmin : ∀ J : ℝ → ℝ, AEStronglyMeasurable J areaμ →
      (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) →
      (∫ x, (x - (1 / 2 : ℝ)) * J x ∂areaμ) = 0 →
      0 ≤ ∫ x, W x * (J x - K x) ∂areaμ) :
    ∃ t : ℝ, ∀ J : ℝ → ℝ, AEStronglyMeasurable J areaμ →
      (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) →
      0 ≤ ∫ x, (W x - t * (x - (1 / 2 : ℝ))) * (J x - K x) ∂areaμ := by
  let moment (J : ℝ → ℝ) : ℝ := ∫ x, (x - (1 / 2 : ℝ)) * J x ∂areaμ
  let cost (J : ℝ → ℝ) : ℝ :=
    (∫ x, W x * J x ∂areaμ) - (∫ x, W x * K x ∂areaμ)
  let S : Set (ℝ × ℝ) := {z | ∃ J : ℝ → ℝ,
    AEStronglyMeasurable J areaμ ∧ (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) ∧
      moment J = z.1 ∧ cost J < z.2}
  have hKi := centered_box_integrable hK hKbox
  have hgKi := centered_moment_integrable hKi
  have hWKi := centered_weighted_box_integrable hW hK hKbox
  have hcost (J : ℝ → ℝ) (hJ : AEStronglyMeasurable J areaμ)
      (hbox : ∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) :
      cost J = ∫ x, W x * (J x - K x) ∂areaμ := by
    have hWJi := centered_weighted_box_integrable hW hJ hbox
    dsimp only [cost]
    rw [← integral_sub hWJi hWKi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hconv : Convex ℝ S := by
    intro z hz z' hz' a b ha hb hab
    obtain ⟨J, hJ, hJbox, hJm, hJcost⟩ := hz
    obtain ⟨L, hL, hLbox, hLm, hLcost⟩ := hz'
    let N : ℝ → ℝ := fun x => a * J x + b * L x
    have hN : AEStronglyMeasurable N areaμ :=
      (hJ.const_mul a).add (hL.const_mul b)
    have hNbox : ∀ᵐ x ∂areaμ, lo ≤ N x ∧ N x ≤ hi := by
      filter_upwards [hJbox, hLbox] with x hx hy
      constructor
      · have hh := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
          (mul_le_mul_of_nonneg_left hy.1 hb)
        dsimp only [N]
        nlinarith [show a * lo + b * lo = lo by rw [← add_mul, hab, one_mul]]
      · have hh := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
        dsimp only [N]
        nlinarith [show a * hi + b * hi = hi by rw [← add_mul, hab, one_mul]]
    have hgJi := centered_moment_integrable (centered_box_integrable hJ hJbox)
    have hgLi := centered_moment_integrable (centered_box_integrable hL hLbox)
    have hWJi := centered_weighted_box_integrable hW hJ hJbox
    have hWLi := centered_weighted_box_integrable hW hL hLbox
    have hNm : moment N = a * moment J + b * moment L := by
      dsimp only [moment, N]
      exact centered_weighted_mix hgJi hgLi a b
    have hNcost : cost N = a * cost J + b * cost L := by
      dsimp only [cost, N]
      rw [centered_weighted_mix hWJi hWLi]
      linear_combination (∫ x, W x * K x ∂areaμ) * hab
    refine ⟨N, hN, hNbox, ?_, ?_⟩
    · change moment N = a * z.1 + b * z'.1
      rw [hNm, hJm, hLm]
    · change cost N < a * z.2 + b * z'.2
      rw [hNcost]
      have hd0 : 0 < z.2 - cost J := sub_pos.mpr hJcost
      have hd1 : 0 < z'.2 - cost L := sub_pos.mpr hLcost
      have hsum : 0 < a * (z.2 - cost J) + b * (z'.2 - cost L) := by
        rcases lt_or_eq_of_le ha with ha' | rfl
        · exact add_pos_of_pos_of_nonneg (mul_pos ha' hd0) (mul_nonneg hb hd1.le)
        · have hb' : b = 1 := by linarith
          simpa [hb'] using hd1
      linarith
  have hzero : (0 : ℝ × ℝ) ∉ S := by
    rintro ⟨J, hJ, hbox, hJm, hJcost⟩
    have hJm' : (∫ x, (x - (1 / 2 : ℝ)) * J x ∂areaμ) = 0 := hJm
    have hh := hmin J hJ hbox hJm'
    rw [← hcost J hJ hbox] at hh
    exact (not_lt_of_ge hh) hJcost
  have hvertical : ((0, 1) : ℝ × ℝ) ∈ S := by
    refine ⟨K, hK, hKbox, hKm, ?_⟩
    simp only [cost, sub_self, zero_lt_one]
  let center : ℝ := (lo + hi) / 2
  let δ : ℝ := (hi - lo) / 24
  have hδ : 0 < δ := div_pos (sub_pos.mpr hlohi) (by norm_num)
  have hδeq : δ * 24 = hi - lo := div_mul_cancel₀ _ (by norm_num)
  let correction (u : ℝ) : ℝ → ℝ :=
    fun x => center + 12 * u * (x - (1 / 2 : ℝ))
  have hcorrmeas (u : ℝ) : AEStronglyMeasurable (correction u) areaμ :=
    (continuous_const.add
      (continuous_const.mul (continuous_id.sub continuous_const))).aestronglyMeasurable
  have hcorrbox (u : ℝ) (hu : |u| < δ) :
      ∀ᵐ x ∂areaμ, lo ≤ correction u x ∧ correction u x ≤ hi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxg : |x - (1 / 2 : ℝ)| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
    have hcor : |12 * u * (x - (1 / 2 : ℝ))| ≤ 6 * |u| := by
      calc
        _ = 12 * |u| * |x - (1 / 2 : ℝ)| := by
          rw [abs_mul, abs_mul]
          norm_num
        _ ≤ 12 * |u| * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hxg (by positivity)
        _ = 6 * |u| := by ring
    have hsmall : |12 * u * (x - (1 / 2 : ℝ))| < (hi - lo) / 2 := by
      nlinarith
    have hh := abs_lt.mp hsmall
    dsimp only [correction, center]
    constructor <;> linarith
  have hgi : Integrable (fun x : ℝ => x - (1 / 2 : ℝ)) areaμ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      ((continuous_id.sub continuous_const).intervalIntegrable 0 1)
  have hcorrm (u : ℝ) : moment (correction u) = u := by
    dsimp only [moment, correction]
    calc
      _ = (∫ x, (x - (1 / 2 : ℝ)) * center ∂areaμ) +
          (12 * u) * (∫ x, (x - (1 / 2 : ℝ)) * (x - (1 / 2 : ℝ)) ∂areaμ) := by
        simpa only [one_mul] using centered_weighted_mix
          (centered_moment_integrable (integrable_const center))
          (centered_moment_integrable hgi) 1 (12 * u)
      _ = u := by rw [centered_constant_moment, centered_square_moment]; ring
  have hWg : Integrable (fun x => W x * (x - (1 / 2 : ℝ))) areaμ := by
    apply (centered_moment_integrable hW).congr
    exact Eventually.of_forall fun x => mul_comm _ _
  let C0 : ℝ := (∫ x, W x * center ∂areaμ) - (∫ x, W x * K x ∂areaμ)
  let C1 : ℝ := 12 * (∫ x, W x * (x - (1 / 2 : ℝ)) ∂areaμ)
  have hcorrcost (u : ℝ) : cost (correction u) = C0 + u * C1 := by
    have hh := centered_weighted_mix (hW.mul_const center) hWg 1 (12 * u)
    simp only [one_mul] at hh
    dsimp only [cost, correction, C0, C1]
    rw [hh]
    ring
  let U : Set (ℝ × ℝ) := {z | |z.1| < δ ∧ C0 + z.1 * C1 < z.2}
  have hopen : IsOpen U := by
    exact (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt (continuous_const.add (continuous_fst.mul continuous_const))
        continuous_snd)
  have hUS : U ⊆ S := by
    intro z hz
    refine ⟨correction z.1, hcorrmeas _, hcorrbox _ hz.1, hcorrm _, ?_⟩
    rw [hcorrcost]
    exact hz.2
  have hint : (interior S).Nonempty := by
    refine ⟨(0, C0 + 1), interior_mono hUS ?_⟩
    rw [hopen.interior_eq]
    change |(0 : ℝ)| < δ ∧ C0 + 0 * C1 < C0 + 1
    simpa only [abs_zero, zero_mul, add_zero] using And.intro hδ (by linarith)
  have hqual (u : ℝ) (hu : |u| < δ) : ∃ v : ℝ, (u, v) ∈ S := by
    refine ⟨C0 + u * C1 + 1, hUS ?_⟩
    exact ⟨hu, by dsimp only; linarith⟩
  obtain ⟨t, ht⟩ := centered_epigraph_separator S hconv hint hzero hvertical δ hδ hqual
  refine ⟨t, ?_⟩
  intro J hJ hJbox
  have hJi := centered_box_integrable hJ hJbox
  have hgJi := centered_moment_integrable hJi
  have hWJi := centered_weighted_box_integrable hW hJ hJbox
  have hdual : t * moment J ≤ cost J := by
    by_contra hn
    have hs : (moment J, cost J + (t * moment J - cost J) / 2) ∈ S :=
      ⟨J, hJ, hJbox, rfl, by linarith⟩
    have hh := ht _ hs
    change t * moment J ≤ cost J + (t * moment J - cost J) / 2 at hh
    linarith
  have hid : (∫ x, (x - (1 / 2 : ℝ)) * (J x - K x) ∂areaμ) = moment J := by
    calc
      _ = ∫ x, (x - (1 / 2 : ℝ)) * J x - (x - (1 / 2 : ℝ)) * K x ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = moment J := by rw [integral_sub hgJi hgKi, hKm, sub_zero]
  have hgdi : Integrable (fun x => (x - (1 / 2 : ℝ)) * (J x - K x)) areaμ := by
    simpa only [Pi.sub_apply] using centered_moment_integrable (hJi.sub hKi)
  have hWdi : Integrable (fun x => W x * (J x - K x)) areaμ := by
    apply (hWJi.sub hWKi).congr
    filter_upwards [] with x
    change W x * J x - W x * K x = W x * (J x - K x)
    ring
  have hformula : (∫ x,
      (W x - t * (x - (1 / 2 : ℝ))) * (J x - K x) ∂areaμ) =
      cost J - t * moment J := by
    calc
      _ = ∫ x, W x * (J x - K x) -
          t * ((x - (1 / 2 : ℝ)) * (J x - K x)) ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = cost J - t * moment J := by
        rw [integral_sub hWdi (hgdi.const_mul t), integral_const_mul,
          hid, ← hcost J hJ hJbox]
  rw [hformula]
  linarith

end RicciFlowSharpEstimate.Analysis
