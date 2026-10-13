/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.InteriorMomentBasis
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Multipliers for two moments in a box

The strict interiority of the prescribed mean supplies constraint qualification
for the zeroth and first moments. A constrained minimum of an integrable linear
cost therefore has two scalar Lagrange multipliers on the whole box.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem box_integrable {J : ℝ → ℝ} {lo hi : ℝ}
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

private theorem box_weight_integrable {W J : ℝ → ℝ} {lo hi : ℝ}
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

private theorem first_moment_integrable_of_integrable {J : ℝ → ℝ}
    (hJ : Integrable J areaμ) : Integrable (fun x => x * J x) areaμ := by
  apply hJ.bdd_mul continuous_id.aestronglyMeasurable (c := 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.le

private theorem integral_weighted_mix {w f g : ℝ → ℝ}
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

private theorem integral_weighted_correction {w ψ0 ψ1 : ℝ → ℝ} {c : ℝ}
    (hc : Integrable (fun x => w x * c) areaμ)
    (h0 : Integrable (fun x => w x * ψ0 x) areaμ)
    (h1 : Integrable (fun x => w x * ψ1 x) areaμ) (u v : ℝ) :
    (∫ x, w x * (c + u * ψ0 x + v * ψ1 x) ∂areaμ) =
      (∫ x, w x * c ∂areaμ) + u * (∫ x, w x * ψ0 x ∂areaμ) +
        v * (∫ x, w x * ψ1 x ∂areaμ) := by
  calc
    _ = ∫ x, (w x * c + u * (w x * ψ0 x)) + v * (w x * ψ1 x) ∂areaμ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      have hsum : Integrable (fun x => w x * c + u * (w x * ψ0 x)) areaμ :=
        hc.add (h0.const_mul u)
      rw [integral_add hsum (h1.const_mul v),
        integral_add hc (h0.const_mul u), integral_const_mul, integral_const_mul]

private theorem normalized_epigraph_separator
    (S : Set ((ℝ × ℝ) × ℝ)) (hconv : Convex ℝ S)
    (hint : (interior S).Nonempty) (hzero : (0 : (ℝ × ℝ) × ℝ) ∉ S)
    (hvertical : ((0, 0), 1) ∈ S) (δ : ℝ) (hδ : 0 < δ)
    (hqual : ∀ u v : ℝ, |u| < δ → |v| < δ → ∃ t : ℝ, ((u, v), t) ∈ S) :
    ∃ a b : ℝ, ∀ z ∈ S, a * z.1.1 + b * z.1.2 ≤ z.2 := by
  obtain ⟨f, hfne, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hconv (fun h => hzero (interior_subset h)) hint
  let p : ℝ := f ((1, 0), 0)
  let q : ℝ := f ((0, 1), 0)
  let r : ℝ := f ((0, 0), 1)
  have hformula (z : (ℝ × ℝ) × ℝ) :
      f z = p * z.1.1 + q * z.1.2 + r * z.2 := by
    have hz : z = z.1.1 • (((1, 0), 0) : (ℝ × ℝ) × ℝ) +
        z.1.2 • (((0, 1), 0) : (ℝ × ℝ) × ℝ) +
        z.2 • (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
      ext <;> simp
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp only [p, q, r]
    ring
  have hnonpos (z : (ℝ × ℝ) × ℝ) (hz : z ∈ S) :
      p * z.1.1 + q * z.1.2 + r * z.2 ≤ 0 := by
    have hh := hsep z hz
    rw [map_zero, hformula] at hh
    exact hh
  have hrle : r ≤ 0 := by simpa using hnonpos _ hvertical
  have hr : r < 0 := by
    by_contra hn
    have hrzero : r = 0 := le_antisymm hrle (le_of_not_gt hn)
    have hh : |δ / 2| < δ := by rw [abs_of_pos (half_pos hδ)]; linarith
    have hhn : |-(δ / 2)| < δ := by simpa only [abs_neg] using hh
    have hz : |(0 : ℝ)| < δ := by simpa using hδ
    obtain ⟨t0p, ht0p⟩ := hqual (δ / 2) 0 hh hz
    obtain ⟨t0n, ht0n⟩ := hqual (-(δ / 2)) 0 hhn hz
    obtain ⟨t1p, ht1p⟩ := hqual 0 (δ / 2) hz hh
    obtain ⟨t1n, ht1n⟩ := hqual 0 (-(δ / 2)) hz hhn
    have h0p := hnonpos _ ht0p
    have h0n := hnonpos _ ht0n
    have h1p := hnonpos _ ht1p
    have h1n := hnonpos _ ht1n
    simp only [hrzero, zero_mul, mul_zero, add_zero, zero_add] at h0p h0n h1p h1n
    have hpδ : p * (δ / 2) = 0 := by nlinarith
    have hqδ : q * (δ / 2) = 0 := by nlinarith
    have hp : p = 0 := (mul_eq_zero.mp hpδ).resolve_right (half_pos hδ).ne'
    have hq : q = 0 := (mul_eq_zero.mp hqδ).resolve_right (half_pos hδ).ne'
    apply hfne
    apply DFunLike.ext
    intro z
    change f z = 0
    rw [hformula, hp, hq, hrzero]
    ring
  refine ⟨-p / r, -q / r, ?_⟩
  intro z hz
  have hdiv := div_nonneg_of_nonpos (hnonpos z hz) hr.le
  have heq : (p * z.1.1 + q * z.1.2 + r * z.2) / r =
      z.2 - ((-p / r) * z.1.1 + (-q / r) * z.1.2) := by
    field_simp [hr.ne]
    ring
  rw [heq] at hdiv
  linarith

/-- A constrained minimum of an integrable linear cost over an almost-everywhere
box, with prescribed mass and first moment, admits scalar multipliers on the
whole box. The moment qualification is proved from the strict interiority of
the prescribed mean, without assuming any separating functional. -/
theorem exists_box_moment_multipliers
    (W K : ℝ → ℝ) (lo hi c : ℝ)
    (hW : Integrable W areaμ)
    (hK : AEStronglyMeasurable K areaμ)
    (hKbox : ∀ᵐ x ∂areaμ, lo ≤ K x ∧ K x ≤ hi)
    (hK0 : (∫ x, K x ∂areaμ) = c)
    (hK1 : (∫ x, x * K x ∂areaμ) = c / 2)
    (hloc : lo < c) (hchi : c < hi)
    (hmin : ∀ J : ℝ → ℝ, AEStronglyMeasurable J areaμ →
      (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) →
      (∫ x, J x ∂areaμ) = c → (∫ x, x * J x ∂areaμ) = c / 2 →
      0 ≤ ∫ x, W x * (J x - K x) ∂areaμ) :
    ∃ a b : ℝ, ∀ J : ℝ → ℝ, AEStronglyMeasurable J areaμ →
      (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) →
      0 ≤ ∫ x, (W x - a - b * x) * (J x - K x) ∂areaμ := by
  let m0 (J : ℝ → ℝ) : ℝ := (∫ x, J x ∂areaμ) - c
  let m1 (J : ℝ → ℝ) : ℝ := (∫ x, x * J x ∂areaμ) - c / 2
  let cost (J : ℝ → ℝ) : ℝ :=
    (∫ x, W x * J x ∂areaμ) - (∫ x, W x * K x ∂areaμ)
  let S : Set ((ℝ × ℝ) × ℝ) := {z | ∃ J : ℝ → ℝ,
    AEStronglyMeasurable J areaμ ∧ (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) ∧
      m0 J = z.1.1 ∧ m1 J = z.1.2 ∧ cost J < z.2}
  have hKi := box_integrable hK hKbox
  have hxKi := first_moment_integrable_of_integrable hKi
  have hWKi := box_weight_integrable hW hK hKbox
  have hcost (J : ℝ → ℝ) (hJ : AEStronglyMeasurable J areaμ)
      (hbox : ∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi) :
      cost J = ∫ x, W x * (J x - K x) ∂areaμ := by
    have hWJi := box_weight_integrable hW hJ hbox
    dsimp only [cost]
    rw [← integral_sub hWJi hWKi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hconv : Convex ℝ S := by
    intro z hz z' hz' a b ha hb hab
    obtain ⟨J, hJ, hJbox, hJ0, hJ1, hJcost⟩ := hz
    obtain ⟨L, hL, hLbox, hL0, hL1, hLcost⟩ := hz'
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
    have hJi := box_integrable hJ hJbox
    have hLi := box_integrable hL hLbox
    have hxJi := first_moment_integrable_of_integrable hJi
    have hxLi := first_moment_integrable_of_integrable hLi
    have hWJi := box_weight_integrable hW hJ hJbox
    have hWLi := box_weight_integrable hW hL hLbox
    have hN0 : m0 N = a * m0 J + b * m0 L := by
      dsimp only [m0, N]
      rw [integral_add (hJi.const_mul a) (hLi.const_mul b),
        integral_const_mul, integral_const_mul]
      linear_combination c * hab
    have hN1 : m1 N = a * m1 J + b * m1 L := by
      dsimp only [m1, N]
      rw [integral_weighted_mix hxJi hxLi]
      linear_combination (c / 2) * hab
    have hNcost : cost N = a * cost J + b * cost L := by
      dsimp only [cost, N]
      rw [integral_weighted_mix hWJi hWLi]
      linear_combination (∫ x, W x * K x ∂areaμ) * hab
    refine ⟨N, hN, hNbox, ?_, ?_, ?_⟩
    · change m0 N = a * z.1.1 + b * z'.1.1
      rw [hN0, hJ0, hL0]
    · change m1 N = a * z.1.2 + b * z'.1.2
      rw [hN1, hJ1, hL1]
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
  have hzero : (0 : (ℝ × ℝ) × ℝ) ∉ S := by
    rintro ⟨J, hJ, hbox, hJ0, hJ1, hJcost⟩
    have hJ0' : (∫ x, J x ∂areaμ) = c := by
      change (∫ x, J x ∂areaμ) - c = 0 at hJ0
      linarith
    have hJ1' : (∫ x, x * J x ∂areaμ) = c / 2 := by
      change (∫ x, x * J x ∂areaμ) - c / 2 = 0 at hJ1
      linarith
    have hh := hmin J hJ hbox hJ0' hJ1'
    rw [← hcost J hJ hbox] at hh
    exact (not_lt_of_ge hh) hJcost
  have hvertical : ((0, 0), 1) ∈ S := by
    refine ⟨K, hK, hKbox, ?_, ?_, ?_⟩
    · simp only [m0, hK0, sub_self]
    · simp only [m1, hK1, sub_self]
    · simp only [cost, sub_self, zero_lt_one]
  obtain ⟨ψ0, ψ1, B, hB, hψ0, hψ1, -, -, -, -, hbound,
    hm00, hm10, hm01, hm11⟩ := exists_contDiff_interior_moment_basis
  have hiψ0 : Integrable ψ0 areaμ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      (hψ0.continuous.intervalIntegrable 0 1)
  have hiψ1 : Integrable ψ1 areaμ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      (hψ1.continuous.intervalIntegrable 0 1)
  have hixψ0 := first_moment_integrable_of_integrable hiψ0
  have hixψ1 := first_moment_integrable_of_integrable hiψ1
  have hWψ0 : Integrable (fun x => W x * ψ0 x) areaμ := by
    apply hW.mul_bdd hψ0.continuous.aestronglyMeasurable (c := B)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbound x).1
  have hWψ1 : Integrable (fun x => W x * ψ1 x) areaμ := by
    apply hW.mul_bdd hψ1.continuous.aestronglyMeasurable (c := B)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbound x).2
  have hm00' : (∫ x, ψ0 x ∂areaμ) = 1 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hm00
  have hm10' : (∫ x, x * ψ0 x ∂areaμ) = 0 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hm10
  have hm01' : (∫ x, ψ1 x ∂areaμ) = 0 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hm01
  have hm11' : (∫ x, x * ψ1 x ∂areaμ) = 1 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hm11
  let ε : ℝ := min (c - lo) (hi - c)
  have hε : 0 < ε := lt_min (sub_pos.mpr hloc) (sub_pos.mpr hchi)
  let δ : ℝ := ε / (4 * B)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (4 * B) = ε := div_mul_cancel₀ _ (by positivity)
  let correction (u v : ℝ) : ℝ → ℝ := fun x => c + u * ψ0 x + v * ψ1 x
  have hcorrmeas (u v : ℝ) : AEStronglyMeasurable (correction u v) areaμ :=
    ((continuous_const.add (continuous_const.mul hψ0.continuous)).add
      (continuous_const.mul hψ1.continuous)).aestronglyMeasurable
  have hcorrbox (u v : ℝ) (hu : |u| < δ) (hv : |v| < δ) :
      ∀ᵐ x ∂areaμ, lo ≤ correction u v x ∧ correction u v x ≤ hi := by
    apply Eventually.of_forall
    intro x
    have hcor : |u * ψ0 x + v * ψ1 x| < ε := by
      calc
        _ ≤ |u| * |ψ0 x| + |v| * |ψ1 x| := by
          simpa only [abs_mul] using abs_add_le (u * ψ0 x) (v * ψ1 x)
        _ ≤ |u| * B + |v| * B := add_le_add
          (mul_le_mul_of_nonneg_left (hbound x).1 (abs_nonneg u))
          (mul_le_mul_of_nonneg_left (hbound x).2 (abs_nonneg v))
        _ < ε := by
          have hu' := mul_lt_mul_of_pos_right hu hB
          have hv' := mul_lt_mul_of_pos_right hv hB
          nlinarith
    have hh := abs_lt.mp hcor
    have hlo : ε ≤ c - lo := min_le_left _ _
    have hhi : ε ≤ hi - c := min_le_right _ _
    dsimp only [correction]
    constructor <;> linarith
  have hcorr0 (u v : ℝ) : m0 (correction u v) = u := by
    have hh := integral_weighted_correction
      (w := fun _ : ℝ => 1) (c := c)
      (by simpa only [one_mul] using (integrable_const c : Integrable (fun _ : ℝ => c) areaμ))
      (by simpa only [one_mul] using hiψ0)
      (by simpa only [one_mul] using hiψ1) u v
    simp only [one_mul, hm00', hm01', mul_one, mul_zero, add_zero] at hh
    have hc : (∫ _ : ℝ, c ∂areaμ) = c := by simp
    dsimp only [m0, correction]
    rw [hh, hc]
    ring
  have hcorr1 (u v : ℝ) : m1 (correction u v) = v := by
    have hxc : Integrable (fun x : ℝ => x * c) areaμ :=
      first_moment_integrable_of_integrable (integrable_const c)
    have hh := integral_weighted_correction hxc hixψ0 hixψ1 u v
    have hxcint : (∫ x : ℝ, x * c ∂areaμ) = c / 2 := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_mul_const]
      norm_num [integral_id]
      ring
    dsimp only [m1, correction]
    rw [hh, hxcint, hm10', hm11']
    ring
  let C0 : ℝ := (∫ x, W x * c ∂areaμ) - (∫ x, W x * K x ∂areaμ)
  let C1 : ℝ := ∫ x, W x * ψ0 x ∂areaμ
  let C2 : ℝ := ∫ x, W x * ψ1 x ∂areaμ
  have hcorrcost (u v : ℝ) : cost (correction u v) = C0 + u * C1 + v * C2 := by
    dsimp only [cost, correction, C0, C1, C2]
    rw [integral_weighted_correction (hW.mul_const c) hWψ0 hWψ1]
    ring
  let U : Set ((ℝ × ℝ) × ℝ) :=
    {z | |z.1.1| < δ ∧ |z.1.2| < δ ∧ C0 + z.1.1 * C1 + z.1.2 * C2 < z.2}
  have hopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_fst.fst.abs) continuous_const
    · apply IsOpen.inter
      · exact isOpen_lt (continuous_fst.snd.abs) continuous_const
      · exact isOpen_lt
          ((continuous_const.add (continuous_fst.fst.mul continuous_const)).add
            (continuous_fst.snd.mul continuous_const)) continuous_snd
  have hUS : U ⊆ S := by
    intro z hz
    refine ⟨correction z.1.1 z.1.2, hcorrmeas _ _, hcorrbox _ _ hz.1 hz.2.1,
      hcorr0 _ _, hcorr1 _ _, ?_⟩
    rw [hcorrcost]
    exact hz.2.2
  have hint : (interior S).Nonempty := by
    refine ⟨((0, 0), C0 + 1), interior_mono hUS ?_⟩
    rw [hopen.interior_eq]
    change |(0 : ℝ)| < δ ∧ |(0 : ℝ)| < δ ∧ C0 + 0 * C1 + 0 * C2 < C0 + 1
    simpa only [abs_zero, zero_mul, add_zero] using And.intro hδ (And.intro hδ (by linarith))
  have hqual (u v : ℝ) (hu : |u| < δ) (hv : |v| < δ) :
      ∃ t : ℝ, ((u, v), t) ∈ S := by
    refine ⟨C0 + u * C1 + v * C2 + 1, hUS ?_⟩
    exact ⟨hu, hv, by dsimp only; linarith⟩
  obtain ⟨a, b, hab⟩ := normalized_epigraph_separator S hconv hint hzero hvertical δ hδ hqual
  refine ⟨a, b, ?_⟩
  intro J hJ hJbox
  have hJi := box_integrable hJ hJbox
  have hxJi := first_moment_integrable_of_integrable hJi
  have hWJi := box_weight_integrable hW hJ hJbox
  have hdual : a * m0 J + b * m1 J ≤ cost J := by
    by_contra hn
    have hp : 0 < (a * m0 J + b * m1 J - cost J) / 2 := by linarith
    have hs : ((m0 J, m1 J), cost J +
        (a * m0 J + b * m1 J - cost J) / 2) ∈ S :=
      ⟨J, hJ, hJbox, rfl, rfl, by linarith⟩
    have hh := hab _ hs
    change a * m0 J + b * m1 J ≤ cost J +
      (a * m0 J + b * m1 J - cost J) / 2 at hh
    linarith
  have hid0 : (∫ x, J x - K x ∂areaμ) = m0 J := by
    rw [integral_sub hJi hKi, hK0]
  have hid1 : (∫ x, x * (J x - K x) ∂areaμ) = m1 J := by
    calc
      _ = ∫ x, x * J x - x * K x ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = m1 J := by rw [integral_sub hxJi hxKi, hK1]
  have hxdi : Integrable (fun x => x * (J x - K x)) areaμ :=
    first_moment_integrable_of_integrable (hJi.sub hKi)
  have hWdi : Integrable (fun x => W x * (J x - K x)) areaμ := by
    apply (hWJi.sub hWKi).congr
    filter_upwards [] with x
    change W x * J x - W x * K x = W x * (J x - K x)
    ring
  have hformula : (∫ x, (W x - a - b * x) * (J x - K x) ∂areaμ) =
      cost J - a * m0 J - b * m1 J := by
    calc
      _ = ∫ x, (W x * (J x - K x) - a * (J x - K x)) -
          b * (x * (J x - K x)) ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = cost J - a * m0 J - b * m1 J := by
        have had : Integrable (fun x => a * (J x - K x)) areaμ :=
          (hJi.sub hKi).const_mul a
        have hsub : Integrable (fun x => W x * (J x - K x) - a * (J x - K x)) areaμ :=
          hWdi.sub had
        rw [integral_sub hsub (hxdi.const_mul b),
          integral_sub hWdi had,
          integral_const_mul, integral_const_mul, hid0, hid1, ← hcost J hJ hJbox]
  rw [hformula]
  linarith

end RicciFlowSharpEstimate.Analysis
