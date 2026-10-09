/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCircleAction
import RicciFlowSharpEstimate.Geometry.RotationalOneForms

/-!
# Stereographic parametrizations of the rotational sphere

Both choices of pole share one actual smooth sphere-valued parametrization. The
formulas adapt Ziyang Qin's historical stereographic invariant-one-form construction.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The positive denominator in the stereographic parametrization. -/
def stereoDenominator (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2 + 4

/-- The stereographic denominator never vanishes. -/
theorem stereoDenominator_pos (p : ℝ × ℝ) : 0 < stereoDenominator p := by
  unfold stereoDenominator
  positivity

/-- Ambient stereographic coordinates centred at the pole of height `epsilon`. -/
def stereoAmbient (epsilon : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![4 * p.1 / stereoDenominator p, 4 * p.2 / stereoDenominator p,
    epsilon * (4 - p.1 ^ 2 - p.2 ^ 2) / stereoDenominator p]

private theorem stereoAmbient_norm (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    ‖stereoAmbient epsilon p‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [stereoAmbient, Fin.sum_univ_succ, mul_pow, div_pow, he]
  have hd := (stereoDenominator_pos p).ne'
  field_simp
  unfold stereoDenominator
  ring

private theorem stereoAmbient_contDiff (epsilon : ℝ) :
    ContDiff ℝ ∞ (stereoAmbient epsilon) := by
  have hd : ContDiff ℝ ∞ stereoDenominator := by unfold stereoDenominator; fun_prop
  unfold stereoAmbient
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact (contDiff_const.mul contDiff_fst).div hd (fun p => (stereoDenominator_pos p).ne')
  · exact (contDiff_const.mul contDiff_snd).div hd (fun p => (stereoDenominator_pos p).ne')
  · exact (contDiff_const.mul ((contDiff_const.sub (contDiff_fst.pow 2)).sub
      (contDiff_snd.pow 2))).div hd (fun p => (stereoDenominator_pos p).ne')

/-- The genuine stereographic sphere map, including its centred pole. -/
def stereoPoint (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) : RotationalSphere :=
  ⟨stereoAmbient epsilon p, mem_sphere_zero_iff_norm.mpr (stereoAmbient_norm epsilon he p)⟩

/-- The sphere-valued parametrization is smooth on the whole coordinate plane. -/
theorem stereoPoint_contMDiff (epsilon : ℝ) (he : epsilon ^ 2 = 1) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (stereoPoint epsilon he) :=
  ContMDiff.codRestrict_sphere (stereoAmbient_contDiff epsilon).contMDiff
    (fun p => (stereoPoint epsilon he p).property)

/-- The parametrization has its stated ambient formula. -/
@[simp] theorem stereoPoint_coe (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    (stereoPoint epsilon he p : EuclideanSpace ℝ (Fin 3)) = stereoAmbient epsilon p := rfl

/-- Height in stereographic coordinates. -/
@[simp] theorem sphereHeight_stereoPoint (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    sphereHeight (stereoPoint epsilon he p) =
      epsilon * (4 - p.1 ^ 2 - p.2 ^ 2) / stereoDenominator p := by
  rw [sphereHeight_apply]
  rfl

/-- The parametrization omits the pole of opposite height. -/
theorem stereoPoint_height_denominator (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    1 + epsilon * sphereHeight (stereoPoint epsilon he p) = 8 / stereoDenominator p := by
  rw [sphereHeight_stereoPoint]
  have hd := (stereoDenominator_pos p).ne'
  field_simp
  unfold stereoDenominator
  nlinarith [he]

/-- The sphere action agrees with ordinary rotation of stereographic coordinates. -/
theorem stereoPoint_planeRotate (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (z : Circle) (p : ℝ × ℝ) :
    stereoPoint epsilon he (z.1.re * p.1 - z.1.im * p.2,
      z.1.im * p.1 + z.1.re * p.2) = circleSphereDiffeo z (stereoPoint epsilon he p) := by
  have hz : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  have hs : (z.1.re * p.1 - z.1.im * p.2) ^ 2 +
      (z.1.im * p.1 + z.1.re * p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    nlinarith [sq_nonneg (z.1.re * p.1 - z.1.im * p.2)]
  have hs' : 4 - (z.1.re * p.1 - z.1.im * p.2) ^ 2 -
      (z.1.im * p.1 + z.1.re * p.2) ^ 2 = 4 - p.1 ^ 2 - p.2 ^ 2 := by
    linarith
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [stereoAmbient, stereoDenominator, hs, hs'] <;> ring

/-- Inverse stereographic coordinates away from the opposite pole. -/
def stereoInversePoint (epsilon : ℝ) (x : RotationalSphere) : ℝ × ℝ :=
  (2 * (x : EuclideanSpace ℝ (Fin 3)) 0 / (1 + epsilon * sphereHeight x),
    2 * (x : EuclideanSpace ℝ (Fin 3)) 1 / (1 + epsilon * sphereHeight x))

/-- Inverse coordinates recover every plane point. -/
@[simp] theorem stereoInversePoint_stereoPoint (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (p : ℝ × ℝ) : stereoInversePoint epsilon (stereoPoint epsilon he p) = p := by
  unfold stereoInversePoint
  rw [stereoPoint_height_denominator]
  have hd := (stereoDenominator_pos p).ne'
  ext <;> simp [stereoAmbient] <;> field_simp <;> ring

/-- Reconstructing a sphere point from inverse coordinates away from the opposite pole. -/
theorem stereoPoint_inverse (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (x : RotationalSphere) (hx : 1 + epsilon * sphereHeight x ≠ 0) :
    stereoPoint epsilon he (stereoInversePoint epsilon x) = x := by
  have hn : (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.property
    have hs := EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin 3))
    rw [hnorm] at hs
    simpa [Fin.sum_univ_succ, add_assoc] using hs.symm
  rw [sphereHeight_apply] at hx
  apply Subtype.ext
  ext i
  rcases sq_eq_one_iff.mp he with rfl | rfl <;> fin_cases i <;>
    simp [stereoAmbient, stereoInversePoint, stereoDenominator, sphereHeight_apply] <;>
    field_simp at hx ⊢ <;>
    first | linear_combination (-4 * (x : EuclideanSpace ℝ (Fin 3)) 0) * hn
          | linear_combination (-4 * (x : EuclideanSpace ℝ (Fin 3)) 1) * hn
          | nlinarith [hn]

private def stereoAmbientDerivative (epsilon : ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (4 / stereoDenominator p) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (8 * p.1 / stereoDenominator p ^ 2) •
          (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ),
      (4 / stereoDenominator p) • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (8 * p.2 / stereoDenominator p ^ 2) •
          (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ),
      (-16 * epsilon / stereoDenominator p ^ 2) •
        (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)])

private theorem stereoAmbient_hasFDerivAt (epsilon : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (stereoAmbient epsilon) (stereoAmbientDerivative epsilon p) p := by
  have h0 := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have h1 := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have hd := ((h0.pow 2).add (h1.pow 2)).add_const 4
  have hne := (stereoDenominator_pos p).ne'
  have hdi := (hasDerivAt_inv hne).comp_hasFDerivAt p hd
  have hx := (h0.const_mul 4).mul hdi
  have hy := (h1.const_mul 4).mul hdi
  have hz := ((((hasFDerivAt_const (4 : ℝ) p).sub (h0.pow 2)).sub
    (h1.pow 2)).const_mul epsilon).mul hdi
  have hraw : HasFDerivAt
      (fun q : ℝ × ℝ => ![4 * q.1 / stereoDenominator q,
        4 * q.2 / stereoDenominator q,
        epsilon * (4 - q.1 ^ 2 - q.2 ^ 2) / stereoDenominator q])
      (ContinuousLinearMap.pi ![
        (4 / stereoDenominator p) • ContinuousLinearMap.fst ℝ ℝ ℝ -
          (8 * p.1 / stereoDenominator p ^ 2) •
            (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ),
        (4 / stereoDenominator p) • ContinuousLinearMap.snd ℝ ℝ ℝ -
          (8 * p.2 / stereoDenominator p ^ 2) •
            (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ),
        (-16 * epsilon / stereoDenominator p ^ 2) •
          (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)]) p := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · convert! hx using 1
      apply ContinuousLinearMap.ext
      intro v
      simp
      field_simp
      ring
    · convert! hy using 1
      apply ContinuousLinearMap.ext
      intro v
      simp
      field_simp
      ring
    · convert! hz using 1
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_add, neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
        Matrix.cons_val, add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
        ContinuousLinearMap.coe_snd', Pi.sub_apply, Nat.add_one_sub_one, pow_one,
        nsmul_eq_mul, Nat.cast_ofNat, neg_smul, smul_neg, Function.comp_apply, zero_sub,
        neg_apply, sub_apply]
      unfold stereoDenominator
      field_simp
      ring
  exact (PiLp.hasFDerivAt_toLp 2 _).comp p hraw

/-- The actual derivative of stereographic coordinates, included in ambient Euclidean space. -/
theorem stereoPoint_dIncl_mfderiv (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (p v : ℝ × ℝ) :
    dIncl (n := 2) (stereoPoint epsilon he p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p v) =
      WithLp.toLp 2 ![
        4 / stereoDenominator p * v.1 -
          8 * p.1 / stereoDenominator p ^ 2 * (p.1 * v.1 + p.2 * v.2),
        4 / stereoDenominator p * v.2 -
          8 * p.2 / stereoDenominator p ^ 2 * (p.1 * v.1 + p.2 * v.2),
        -16 * epsilon / stereoDenominator p ^ 2 * (p.1 * v.1 + p.2 * v.2)] := by
  have hc := (stereoPoint_contMDiff epsilon he).mdifferentiableAt (x := p) (by simp)
  have hi := (contMDiff_coe_sphere (m := ∞) (n := 2)
    (E := EuclideanSpace ℝ (Fin 3))).mdifferentiableAt
    (x := stereoPoint epsilon he p) (by simp)
  have hchain := mfderiv_comp_apply (x := p) (f := stereoPoint epsilon he)
    (g := ((↑) : RotationalSphere → EuclideanSpace ℝ (Fin 3))) hi hc v
  apply hchain.symm.trans
  change mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
    (stereoAmbient epsilon) p v = _
  rw [mfderiv_eq_fderiv, (stereoAmbient_hasFDerivAt epsilon p).fderiv]
  change stereoAmbientDerivative epsilon p v = _
  ext i
  fin_cases i <;> simp [stereoAmbientDerivative] <;> ring

/-- The actual stereographic tangent map is injective, including at the centred pole. -/
theorem stereoPoint_mfderiv_injective (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p v = 0 at hv
  change ℝ × ℝ at v
  have hd := (stereoDenominator_pos p).ne'
  have he0 : epsilon ≠ 0 := by
    rintro rfl
    norm_num at he
  have hall := stereoPoint_dIncl_mfderiv epsilon he p v
  rw [hv, map_zero] at hall
  have h2 : -16 * epsilon / stereoDenominator p ^ 2 * (p.1 * v.1 + p.2 * v.2) = 0 := by
    simpa using (congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 2) hall).symm
  have hdot : p.1 * v.1 + p.2 * v.2 = 0 :=
    (mul_eq_zero.mp h2).resolve_left
      (div_ne_zero (mul_ne_zero (by norm_num) he0) (pow_ne_zero 2 hd))
  have h0 : 4 / stereoDenominator p * v.1 = 0 := by
    simpa [hdot] using (congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 0) hall).symm
  have h1 : 4 / stereoDenominator p * v.2 = 0 := by
    simpa [hdot] using (congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 1) hall).symm
  change v = (0 : ℝ × ℝ)
  exact Prod.ext
    ((mul_eq_zero.mp h0).resolve_left (div_ne_zero (by norm_num) hd))
    ((mul_eq_zero.mp h1).resolve_left (div_ne_zero (by norm_num) hd))

/-- Every sphere tangent is the derivative of a stereographic coordinate tangent. -/
theorem stereoPoint_mfderiv_surjective (epsilon : ℝ) (he : epsilon ^ 2 = 1) (p : ℝ × ℝ) :
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p) := by
  exact (LinearEquiv.ofInjectiveOfFinrankEq
    (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p).toLinearMap
    (stereoPoint_mfderiv_injective epsilon he p) (by
      change Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
      simp)).surjective

/-- The actual pullback of the height differential in stereographic coordinates. -/
theorem heightOneForm_stereoPoint_mfderiv (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (p v : ℝ × ℝ) :
    heightOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 =>
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p v) =
        -16 * epsilon * (p.1 * v.1 + p.2 * v.2) / stereoDenominator p ^ 2 := by
  rw [heightOneForm_apply_dIncl, stereoPoint_dIncl_mfderiv]
  simp
  ring

/-- The actual pullback of the angular differential in stereographic coordinates. -/
theorem sphereAzimuthalOneForm_stereoPoint_mfderiv (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (p v : ℝ × ℝ) :
    sphereAzimuthalOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 =>
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p v) =
        16 * (p.1 * v.2 - p.2 * v.1) / stereoDenominator p ^ 2 := by
  rw [sphereAzimuthalOneForm_apply, stereoPoint_dIncl_mfderiv]
  simp [stereoAmbient]
  have hd := (stereoDenominator_pos p).ne'
  field_simp [hd]
  ring

end RicciFlowSharpEstimate.Geometry
