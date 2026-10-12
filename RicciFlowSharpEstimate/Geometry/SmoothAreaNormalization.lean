/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ReciprocalAreaGeometry
import RicciFlowSharpEstimate.Geometry.RotationalPoleData
import RicciFlowSharpEstimate.Analysis.SmoothIntervalInverse
import RicciFlowSharpEstimate.Analysis.SmoothQuotient

/-!
# Smooth normalization of an original rotational profile

Every smooth balanced positive rotational profile determines a smooth extension
of its actual area curvature. Its height primitive is the smooth inverse used
for all transported probes. Both inverse laws, curvature, moments and warping
coefficients agree with the original profile on the complete physical intervals.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.ReciprocalArea

open scoped ContDiff

/-- The actual normalized coordinate of a smooth profile is globally smooth. -/
theorem coordinate_contDiff (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (coordinate a) :=
  (Analysis.SecondPrimitive.integral_contDiff a ha (-1)).div_const (length a)

end RicciFlowSharpEstimate.Geometry.ReciprocalArea

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set MeasureTheory
open scoped ContDiff

/-- A smooth extension of the actual normalized curvature of the original profile.
The coordinate is fixed by D; no metric, probe, independent jet or action is supplied. -/
structure AreaNormalization (D : PoleData) where
  curvature : ℝ → ℝ
  curvature_contDiff : ContDiff ℝ ∞ curvature
  curvature_eq : EqOn curvature (ReciprocalArea.curvature D.a) (Icc (0 : ℝ) 1)

/-- Every original pole profile produces a smooth extension of its actual
normalized curvature, with no additional geometric input. -/
theorem nonempty_areaNormalization (D : PoleData) : Nonempty (AreaNormalization D) := by
  have hcoordinate := ReciprocalArea.coordinate_contDiff D.a D.a_contDiff
  have hderivPos : ∀ v ∈ Icc (-1 : ℝ) 1,
      0 < deriv (ReciprocalArea.coordinate D.a) v := by
    intro v hv
    rw [(ReciprocalArea.coordinate_hasDerivAt D.a D.a_contDiff.continuous v).deriv]
    exact div_pos (D.a_pos v hv)
      (ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos)
  obtain ⟨W, hW, _, hWX, _, _, _, _⟩ := Analysis.exists_contDiff_inverse_on_Icc
    (ReciprocalArea.coordinate D.a) (-1) 1 (by norm_num) hcoordinate hderivPos
  have hWphysical (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      W x = ReciprocalArea.inverse D.a x := by
    calc
      W x = W (ReciprocalArea.coordinate D.a (ReciprocalArea.inverse D.a x)) :=
        congrArg W (ReciprocalArea.coordinate_inverse D.a
          D.a_contDiff.continuous D.a_pos x hx).symm
      _ = ReciprocalArea.inverse D.a x := hWX _
        (ReciprocalArea.inverse_mem D.a D.a_contDiff.continuous D.a_pos x)
  have hdenom (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : D.a (W x) ≠ 0 := by
    rw [hWphysical x hx]
    exact (D.a_pos _
      (ReciprocalArea.inverse_mem D.a D.a_contDiff.continuous D.a_pos x)).ne'
  obtain ⟨K, hK, hmul⟩ := Analysis.exists_contDiff_mul_eq_on_Icc
    0 1 zero_le_one (fun x => D.a (W x)) (fun _ => ReciprocalArea.length D.a)
    (D.a_contDiff.comp hW) contDiff_const hdenom
  refine ⟨⟨K, hK, ?_⟩⟩
  intro x hx
  change K x = ReciprocalArea.length D.a / D.a (ReciprocalArea.inverse D.a x)
  rw [← hWphysical x hx]
  apply (eq_div_iff (hdenom x hx)).mpr
  simpa only [mul_comm] using hmul x hx

/-- A chosen smooth normalization of the actual original profile. -/
def areaNormalization (D : PoleData) : AreaNormalization D :=
  Classical.choice (nonempty_areaNormalization D)

namespace AreaNormalization

variable {D : PoleData}

/-- The chosen smooth inverse extension is the actual curvature primitive. -/
def inverse (N : AreaNormalization D) : ℝ → ℝ := AreaProfile.heightCoordinate N.curvature

/-- The probe is transported by the same inverse for every input function. -/
def probe (N : AreaNormalization D) (R : ℝ → ℝ) : ℝ → ℝ := R ∘ N.inverse

/-- Normalized curvature is positive throughout the physical area interval. -/
theorem curvature_pos (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < N.curvature x := by
  rw [N.curvature_eq hx]
  exact ReciprocalArea.curvature_pos D.a D.a_contDiff.continuous D.a_pos x

private theorem integral_curvature_eq (N : AreaNormalization D) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..x, N.curvature t) =
      ∫ t in (0 : ℝ)..x, ReciprocalArea.curvature D.a t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  exact N.curvature_eq ⟨ht.1, ht.2.trans hx.2⟩

/-- Every smooth normalization has the actual zeroth curvature moment. -/
theorem integral_curvature (N : AreaNormalization D) :
    (∫ x in (0 : ℝ)..1, N.curvature x) = 2 := by
  rw [N.integral_curvature_eq 1 (by norm_num)]
  exact ReciprocalArea.integral_curvature D.a D.a_contDiff.continuous D.a_pos

/-- Balance of the original profile gives the actual first curvature moment. -/
theorem integral_mul_curvature (N : AreaNormalization D) :
    (∫ x in (0 : ℝ)..1, x * N.curvature x) = 1 := by
  calc
    (∫ x in (0 : ℝ)..1, x * N.curvature x) =
        ∫ x in (0 : ℝ)..1, x * ReciprocalArea.curvature D.a x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      dsimp only
      rw [N.curvature_eq hx]
    _ = 1 := ReciprocalArea.integral_mul_curvature D.a
      D.a_contDiff.continuous D.a_pos D.balance_eq

/-- The common inverse used by all probes is smooth on the whole real line. -/
theorem inverse_contDiff (N : AreaNormalization D) : ContDiff ℝ ∞ N.inverse :=
  AreaProfile.heightCoordinate_contDiff N.curvature N.curvature_contDiff

/-- The common inverse has curvature as its derivative on the whole real line. -/
theorem inverse_hasDerivAt (N : AreaNormalization D) (x : ℝ) :
    HasDerivAt N.inverse (N.curvature x) x :=
  AreaProfile.heightCoordinate_hasDerivAt N.curvature N.curvature_contDiff.continuous x

/-- The curvature primitive inverts the actual coordinate, including both poles. -/
theorem inverse_coordinate (N : AreaNormalization D) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) : N.inverse (ReciprocalArea.coordinate D.a v) = v := by
  change -1 + (∫ t in (0 : ℝ)..ReciprocalArea.coordinate D.a v, N.curvature t) = v
  rw [N.integral_curvature_eq _
    (ReciprocalArea.coordinate_mapsTo D.a D.a_contDiff.continuous D.a_pos hv)]
  exact ReciprocalArea.heightCoordinate_coordinate D.a D.a_contDiff.continuous D.a_pos v hv

/-- On the physical interval the smooth primitive is the actual clamped inverse. -/
theorem inverse_eq (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    N.inverse x = ReciprocalArea.inverse D.a x := by
  calc
    N.inverse x = N.inverse
        (ReciprocalArea.coordinate D.a (ReciprocalArea.inverse D.a x)) :=
      congrArg N.inverse (ReciprocalArea.coordinate_inverse D.a
        D.a_contDiff.continuous D.a_pos x hx).symm
    _ = ReciprocalArea.inverse D.a x := N.inverse_coordinate _
      (ReciprocalArea.inverse_mem D.a D.a_contDiff.continuous D.a_pos x)

/-- The smooth inverse takes the entire physical area interval to physical heights. -/
theorem inverse_mem (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    N.inverse x ∈ Icc (-1 : ℝ) 1 := by
  rw [N.inverse_eq x hx]
  exact ReciprocalArea.inverse_mem D.a D.a_contDiff.continuous D.a_pos x

/-- The actual coordinate inverts the smooth primitive throughout the physical interval. -/
theorem coordinate_inverse (N : AreaNormalization D) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) : ReciprocalArea.coordinate D.a (N.inverse x) = x := by
  rw [N.inverse_eq x hx]
  exact ReciprocalArea.coordinate_inverse D.a D.a_contDiff.continuous D.a_pos x hx

@[simp]
theorem inverse_zero (N : AreaNormalization D) : N.inverse 0 = -1 :=
  AreaProfile.heightCoordinate_zero N.curvature

@[simp]
theorem inverse_one (N : AreaNormalization D) : N.inverse 1 = 1 :=
  AreaProfile.heightCoordinate_one N.curvature N.integral_curvature

/-- The smooth curvature retains the original reciprocal profile and actual scale. -/
theorem curvature_coordinate (N : AreaNormalization D) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    N.curvature (ReciprocalArea.coordinate D.a v) = ReciprocalArea.length D.a / D.a v := by
  rw [N.curvature_eq
    (ReciprocalArea.coordinate_mapsTo D.a D.a_contDiff.continuous D.a_pos hv)]
  exact ReciprocalArea.curvature_coordinate D.a D.a_contDiff.continuous D.a_pos v hv

/-- The complete physical warping coefficient has the exact original area scale. -/
theorem warp_coordinate (N : AreaNormalization D) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warp N.curvature (ReciprocalArea.coordinate D.a v) =
      warp D.a v / ReciprocalArea.length D.a := by
  have hx := ReciprocalArea.coordinate_mapsTo D.a D.a_contDiff.continuous D.a_pos hv
  have hkernel :
      (∫ t in (0 : ℝ)..ReciprocalArea.coordinate D.a v,
        (ReciprocalArea.coordinate D.a v - t) * N.curvature t) =
      ∫ t in (0 : ℝ)..ReciprocalArea.coordinate D.a v,
        (ReciprocalArea.coordinate D.a v - t) * ReciprocalArea.curvature D.a t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    dsimp only
    rw [N.curvature_eq ⟨ht.1, ht.2.trans hx.2⟩]
  calc
    AreaProfile.warp N.curvature (ReciprocalArea.coordinate D.a v) =
        AreaProfile.warp (ReciprocalArea.curvature D.a) (ReciprocalArea.coordinate D.a v) := by
      simp only [AreaProfile.warp, hkernel]
    _ = warp D.a v / ReciprocalArea.length D.a :=
      ReciprocalArea.warp_coordinate D.a D.a_contDiff.continuous D.a_pos D.balance_eq v hv

/-- The actual warping slope is minus twice the original height. -/
theorem warpSlope_coordinate (N : AreaNormalization D) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warpSlope N.curvature (ReciprocalArea.coordinate D.a v) = -2 * v := by
  rw [AreaProfile.warpSlope_eq_neg_two_height]
  change -2 * N.inverse (ReciprocalArea.coordinate D.a v) = -2 * v
  rw [N.inverse_coordinate v hv]

end AreaNormalization

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
