/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BalancedSphereMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Height and angular coordinates on the rotational sphere

The height cylinder parametrizes the sphere away from its poles. Its actual
manifold derivative pulls the reconstructed metric back to the diagonal form
`(a² / warp a) dv² + warp a dθ²` in physical Euclidean coordinates.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open Set TopologicalSpace
open scoped Manifold ContDiff RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The open height cylinder, with unrestricted real angular coordinate. -/
def cylinderDomain : Opens (EuclideanSpace ℝ (Fin 2)) where
  carrier := {q | q 0 ∈ Ioo (-1 : ℝ) 1}
  is_open' := isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)

private theorem cylinder_radius_sq_pos (q : cylinderDomain) : 0 < 1 - q.val 0 ^ 2 := by
  have h := q.property
  change -1 < q.val 0 ∧ q.val 0 < 1 at h
  nlinarith

private def cylinderAmbient (q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.sqrt (1 - q 0 ^ 2) * Real.cos (q 1),
    Real.sqrt (1 - q 0 ^ 2) * Real.sin (q 1), q 0]

private theorem cylinderAmbient_norm (q : cylinderDomain) : ‖cylinderAmbient q‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [cylinderAmbient, Fin.sum_univ_succ, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  have hs := Real.sq_sqrt (cylinder_radius_sq_pos q).le
  have ht := Real.sin_sq_add_cos_sq (q.val 1)
  nlinarith [congrArg (fun t : ℝ => Real.sqrt (1 - q.val 0 ^ 2) ^ 2 * t) ht]

/-- The actual height-cylinder map to the fixed unit sphere. -/
def cylinderMap (q : cylinderDomain) : RotationalSphere :=
  ⟨cylinderAmbient q, mem_sphere_zero_iff_norm.mpr (cylinderAmbient_norm q)⟩

/-- The ambient coordinates of the height-cylinder map. -/
theorem cylinderMap_coe (q : cylinderDomain) :
    (cylinderMap q : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 ![Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1),
        Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1), q.val 0] := rfl

/-- The height parameter is the actual height on the sphere. -/
@[simp] theorem sphereHeight_cylinderMap (q : cylinderDomain) :
    sphereHeight (cylinderMap q) = q.val 0 := by
  rw [sphereHeight_apply, cylinderMap_coe]
  rfl

private theorem cylinderAmbient_contDiffAt (q : cylinderDomain) :
    ContDiffAt ℝ ∞ cylinderAmbient q.val := by
  have hv : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) => p 0) q.val :=
    contDiffAt_piLp_apply 2
  have ht : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) => p 1) q.val :=
    contDiffAt_piLp_apply 2
  have hr := (contDiffAt_const.sub (hv.pow 2)).sqrt (cylinder_radius_sq_pos q).ne'
  apply contDiffAt_piLp'
  intro i
  fin_cases i
  · exact hr.mul ht.cos
  · exact hr.mul ht.sin
  · exact hv

/-- The height-cylinder map is smooth throughout its open domain. -/
theorem cylinderMap_contMDiff : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) ∞
    cylinderMap := by
  apply ContMDiff.codRestrict_sphere
  intro q
  exact (cylinderAmbient_contDiffAt q).contMDiffAt.comp q
    contMDiff_subtype_val.contMDiffAt

private def cylinderAmbientDerivative (q : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (-q 0 / Real.sqrt (1 - q 0 ^ 2) * Real.cos (q 1)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 -
        (Real.sqrt (1 - q 0 ^ 2) * Real.sin (q 1)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1,
      (-q 0 / Real.sqrt (1 - q 0 ^ 2) * Real.sin (q 1)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        (Real.sqrt (1 - q 0 ^ 2) * Real.cos (q 1)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1,
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0])

private theorem cylinderAmbient_hasFDerivAt (q : cylinderDomain) :
    HasFDerivAt cylinderAmbient (cylinderAmbientDerivative q) q.val := by
  have hv := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 q.val (0 : Fin 2)
  have ht := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 q.val (1 : Fin 2)
  have hr₀ := ((hasFDerivAt_const (1 : ℝ) q.val).sub (hv.pow 2)).sqrt
    (cylinder_radius_sq_pos q).ne'
  have hr : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin 2) => Real.sqrt (1 - p 0 ^ 2))
      ((-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)
      q.val := by
    convert! hr₀ using 1
    ext V
    simp only [smul_apply, sub_apply, zero_apply, smul_eq_mul, Pi.sub_apply]
    ring
  have hx := hr.mul ht.cos
  have hy := hr.mul ht.sin
  have hraw : HasFDerivAt
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        ![Real.sqrt (1 - p 0 ^ 2) * Real.cos (p 1),
          Real.sqrt (1 - p 0 ^ 2) * Real.sin (p 1), p 0])
      (ContinuousLinearMap.pi ![
        (-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) •
            PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 -
          (Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) •
            PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1,
        (-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) •
            PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
          (Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) •
            PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1,
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0]) q.val := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · convert! hx using 1
      ext V
      simp
      ring
    · convert! hy using 1
      ext V
      simp
      ring
    · exact hv
  exact (PiLp.hasFDerivAt_toLp 2 _).comp q.val hraw

/-- The actual manifold derivative, viewed in the ambient Euclidean space. -/
theorem cylinderMap_dIncl_mfderiv (q : cylinderDomain)
    (V : EuclideanSpace ℝ (Fin 2)) :
    dIncl (n := 2) (cylinderMap q)
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V) =
      WithLp.toLp 2 ![
        (-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) * V 0 -
          (Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) * V 1,
        (-q.val 0 / Real.sqrt (1 - q.val 0 ^ 2) * Real.sin (q.val 1)) * V 0 +
          (Real.sqrt (1 - q.val 0 ^ 2) * Real.cos (q.val 1)) * V 1,
        V 0] := by
  change TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) q at V
  have hc := cylinderMap_contMDiff.mdifferentiableAt (x := q) (by simp)
  have hi := (contMDiff_coe_sphere (m := ∞) (n := 2)
    (E := EuclideanSpace ℝ (Fin 3))).mdifferentiableAt
    (x := cylinderMap q) (by simp)
  have hchain := mfderiv_comp_apply (x := q) (f := cylinderMap)
    (g := ((↑) : RotationalSphere → EuclideanSpace ℝ (Fin 3))) hi hc V
  apply hchain.symm.trans
  change mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (cylinderAmbient ∘ Subtype.val) q V = _
  rw [mfderiv_comp_apply (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) q
    (cylinderAmbient_hasFDerivAt q).differentiableAt.mdifferentiableAt
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), mfderiv_subtype_val_apply,
    mfderiv_eq_fderiv, (cylinderAmbient_hasFDerivAt q).fderiv]
  change cylinderAmbientDerivative q.val (show EuclideanSpace ℝ (Fin 2) from V) = _
  change EuclideanSpace ℝ (Fin 2) at V
  ext i
  fin_cases i <;> simp [cylinderAmbientDerivative]

private theorem heightOneForm_cylinderMap_mfderiv (q : cylinderDomain)
    (V : EuclideanSpace ℝ (Fin 2)) :
    heightOneForm (cylinderMap q) (fun _ : Fin 1 =>
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V) = V 0 := by
  rw [heightOneForm_apply, mvfderiv_real_eq_mfderiv]
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
    (cylinderMap q) _ = _
  rw [mfderiv_innerCoordFun, cylinderMap_dIncl_mfderiv]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

/-- The round metric in the actual height-cylinder coordinates. -/
theorem cylinderMap_round_inner (q : cylinderDomain) (V W : EuclideanSpace ℝ (Fin 2)) :
    HeightMetricCoefficients.round.inner (cylinderMap q)
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V)
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q W) =
        (1 / (1 - q.val 0 ^ 2)) * V 0 * W 0 + (1 - q.val 0 ^ 2) * V 1 * W 1 := by
  rw [roundMetric_inner, cylinderMap_dIncl_mfderiv, cylinderMap_dIncl_mfderiv]
  have hr := (cylinder_radius_sq_pos q).ne'
  have hs := Real.sq_sqrt (cylinder_radius_sq_pos q).le
  have ht := Real.cos_sq_add_sin_sq (q.val 1)
  simp only [PiLp.inner_apply, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    RCLike.inner_apply, conj_trivial]
  calc
    _ = (q.val 0 ^ 2 / Real.sqrt (1 - q.val 0 ^ 2) ^ 2 *
          (Real.cos (q.val 1) ^ 2 + Real.sin (q.val 1) ^ 2) + 1) * V 0 * W 0 +
        Real.sqrt (1 - q.val 0 ^ 2) ^ 2 *
          (Real.cos (q.val 1) ^ 2 + Real.sin (q.val 1) ^ 2) * V 1 * W 1 := by ring
    _ = _ := by
      rw [ht, hs]
      field_simp [hr]
      ring

/-- The height-cylinder map has injective differential at every point. -/
theorem cylinderMap_mfderiv_injective (q : cylinderDomain) :
    Function.Injective
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro V hV
  change mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V = 0 at hV
  have hround := cylinderMap_round_inner q V V
  rw [hV] at hround
  simp only [map_zero] at hround
  change EuclideanSpace ℝ (Fin 2) at V
  have hp := cylinder_radius_sq_pos q
  have hi : 0 < (1 : ℝ) / (1 - q.val 0 ^ 2) := div_pos zero_lt_one hp
  have h0 : V 0 = 0 := by
    have hnonneg := mul_nonneg hp.le (sq_nonneg (V 1))
    have hle : (1 / (1 - q.val 0 ^ 2)) * (V 0) ^ 2 ≤ 0 := by nlinarith [hround]
    have hs : (V 0) ^ 2 ≤ 0 := (mul_le_mul_iff_left₀ hi).mp (by simpa [mul_comm] using hle)
    nlinarith [sq_nonneg (V 0)]
  have h1 : V 1 = 0 := by
    rw [h0] at hround
    have hle : (1 - q.val 0 ^ 2) * (V 1) ^ 2 ≤ 0 := by nlinarith [hround]
    have hs : (V 1) ^ 2 ≤ 0 := (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm] using hle)
    nlinarith [sq_nonneg (V 1)]
  change V = (0 : EuclideanSpace ℝ (Fin 2))
  ext i
  fin_cases i <;> simp [h0, h1]

namespace RotationalProfile.PoleData

/-- The reconstructed warping coefficient is positive at every cylinder point. -/
theorem cylinderMap_warp_pos (D : PoleData) (q : cylinderDomain) :
    0 < warp D.a (q.val 0) :=
  warp_pos_of_balance D.a D.a_contDiff.continuous D.a_pos D.balance_eq _ q.property

/-- The actual pullback of the accepted sphere metric in height and angle coordinates. -/
theorem cylinderMap_metric_inner (D : PoleData) (q : cylinderDomain)
    (V W : EuclideanSpace ℝ (Fin 2)) :
    D.metric.inner (cylinderMap q)
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q V)
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) cylinderMap q W) =
        (D.a (q.val 0) ^ 2 / warp D.a (q.val 0)) * V 0 * W 0 +
          warp D.a (q.val 0) * V 1 * W 1 := by
  rw [D.metric_inner, sphereHeight_cylinderMap, cylinderMap_round_inner,
    heightOneForm_cylinderMap_mfderiv, heightOneForm_cylinderMap_mfderiv,
    D.warp_factor]
  have hb := (D.b_pos (q.val 0) ⟨q.property.1.le, q.property.2.le⟩).ne'
  have hr := (cylinder_radius_sq_pos q).ne'
  have hf := D.radial_factor (q.val 0)
  have hcoef : D.b (q.val 0) * (1 / (1 - q.val 0 ^ 2)) +
      D.c (q.val 0) / D.b (q.val 0) =
        D.a (q.val 0) ^ 2 / ((1 - q.val 0 ^ 2) * D.b (q.val 0)) := by
    field_simp
    nlinarith [hf]
  calc
    _ = (D.b (q.val 0) * (1 / (1 - q.val 0 ^ 2)) +
          D.c (q.val 0) / D.b (q.val 0)) * V 0 * W 0 +
        ((1 - q.val 0 ^ 2) * D.b (q.val 0)) * V 1 * W 1 := by ring
    _ = _ := by rw [hcoef]

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
