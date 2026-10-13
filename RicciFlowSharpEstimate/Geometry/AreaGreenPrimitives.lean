/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.UnitIntervalGreen
import RicciFlowSharpEstimate.Geometry.AreaProfile

/-!
# Dirichlet kernels for the original curvature primitives

The difference of two integrable curvatures with equal area moments has
its actual warp and slope represented by the unit-interval Green kernels.
The warp kernel vanishes at both poles; no probe boundary values enter.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory

private theorem green_intervalIntegrable {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo (0 : ℝ) 1)) : IntervalIntegrable u volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hu

private theorem green_intervalIntegrable_initial {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable u volume 0 x := by
  apply (green_intervalIntegrable hu).mono_set
  rw [uIcc_of_le hx.1, uIcc_of_le zero_le_one]
  exact Icc_subset_Icc le_rfl hx.2

private theorem green_difference_moment_zero
    (K L : ℝ → ℝ) (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (hzero : (∫ s in (0 : ℝ)..1, K s) = ∫ s in (0 : ℝ)..1, L s)
    (hfirst : (∫ s in (0 : ℝ)..1, s * K s) = ∫ s in (0 : ℝ)..1, s * L s) :
    (∫ s in (0 : ℝ)..1, (1 - s) * (K s - L s)) = 0 := by
  have hKi := green_intervalIntegrable hK
  have hLi := green_intervalIntegrable hL
  have hKx : IntervalIntegrable (fun s : ℝ => s * K s) volume 0 1 :=
    hKi.continuousOn_mul continuous_id.continuousOn
  have hLx : IntervalIntegrable (fun s : ℝ => s * L s) volume 0 1 :=
    hLi.continuousOn_mul continuous_id.continuousOn
  calc
    _ = ∫ s in (0 : ℝ)..1, (K s - L s) - (s * K s - s * L s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = 0 := by
      rw [intervalIntegral.integral_sub (hKi.sub hLi) (hKx.sub hLx),
        intervalIntegral.integral_sub hKi hLi,
        intervalIntegral.integral_sub hKx hLx, hzero, hfirst]
      ring

/-- Equal curvature moments give a both-pole Green representation of the
actual warp difference for merely integrable curvature. -/
theorem warp_sub_eq_integral_unitDirichletKernel
    (K L : ℝ → ℝ) (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (hzero : (∫ s in (0 : ℝ)..1, K s) = ∫ s in (0 : ℝ)..1, L s)
    (hfirst : (∫ s in (0 : ℝ)..1, s * K s) = ∫ s in (0 : ℝ)..1, s * L s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp K x - warp L x =
      2 * ∫ s in (0 : ℝ)..1, Analysis.unitDirichletKernel x s * (K s - L s) := by
  have hKi : IntervalIntegrable (fun s => (x - s) * K s) volume 0 x :=
    (green_intervalIntegrable_initial hK hx).continuousOn_mul
    (continuous_const.sub continuous_id).continuousOn
  have hLi : IntervalIntegrable (fun s => (x - s) * L s) volume 0 x :=
    (green_intervalIntegrable_initial hL hx).continuousOn_mul
    (continuous_const.sub continuous_id).continuousOn
  rw [Analysis.integral_unitDirichletKernel (fun s => K s - L s) (hK.sub hL) x hx,
    green_difference_moment_zero K L hK hL hzero hfirst, mul_zero, zero_sub]
  simp only [mul_sub, intervalIntegral.integral_sub hKi hLi, warp]
  ring

/-- The same exact-moment difference has its actual slope represented by
the corresponding bounded Green slope kernel. -/
theorem warpSlope_sub_eq_integral_unitDirichletSlopeKernel
    (K L : ℝ → ℝ) (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (hzero : (∫ s in (0 : ℝ)..1, K s) = ∫ s in (0 : ℝ)..1, L s)
    (hfirst : (∫ s in (0 : ℝ)..1, s * K s) = ∫ s in (0 : ℝ)..1, s * L s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warpSlope K x - warpSlope L x =
      2 * ∫ s in (0 : ℝ)..1, Analysis.unitDirichletSlopeKernel x s * (K s - L s) := by
  rw [Analysis.integral_unitDirichletSlopeKernel (fun s => K s - L s) (hK.sub hL) x hx,
    green_difference_moment_zero K L hK hL hzero hfirst, zero_sub,
    intervalIntegral.integral_sub
      (green_intervalIntegrable_initial hK hx) (green_intervalIntegrable_initial hL hx)]
  unfold warpSlope
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
