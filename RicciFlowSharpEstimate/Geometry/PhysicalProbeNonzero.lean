/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalOneForms

/-!
# Physical nonvanishing of rotational probes

The original meridional and azimuthal sections vanish exactly when their smooth
real coefficient vanishes on the open physical height interval. Their values at
the poles are already zero by the original geometric producer laws.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open Set
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem sphereHeight_sq_eq_one_of_not_mem_Ioo (x : RotationalSphere)
    (hx : sphereHeight x ∉ Ioo (-1 : ℝ) 1) : sphereHeight x ^ 2 = 1 := by
  have hz := sphereHeight_mem_Icc x
  rcases eq_or_lt_of_le hz.1 with hs | hs
  · rw [← hs]
    norm_num
  · have hn : sphereHeight x = 1 :=
      le_antisymm hz.2 (le_of_not_gt (fun hn => hx ⟨hs, hn⟩))
    rw [hn]
    norm_num

namespace RotationalProfile.PoleData

/-- The original meridional section vanishes exactly when its coefficient
vanishes throughout the open physical height interval. -/
theorem meridionalOneForm_eq_zero_iff (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    D.meridionalOneForm r hr = 0 ↔ ∀ v ∈ Ioo (-1 : ℝ) 1, r v = 0 := by
  constructor
  · intro h v hv
    let q : cylinderDomain := ⟨WithLp.toLp 2 ![v, 0], hv⟩
    let V : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    have hev := D.meridionalOneForm_cylinderMap_mfderiv r hr q V
    rw [h] at hev
    have hprod : D.a v * r v = 0 := by
      simpa [q, V] using hev.symm
    exact (mul_eq_zero.mp hprod).resolve_left (D.a_pos v ⟨hv.1.le, hv.2.le⟩).ne'
  · intro h
    apply DFunLike.ext
    intro x
    change D.meridionalOneForm r hr x = 0
    by_cases hx : sphereHeight x ∈ Ioo (-1 : ℝ) 1
    · apply ContinuousMultilinearMap.ext
      intro slots
      change D.meridionalOneForm r hr x slots = 0
      rw [meridionalOneForm_apply, h _ hx, mul_zero, zero_mul]
    · exact D.meridionalOneForm_eq_zero_at_pole r hr x
        (sphereHeight_sq_eq_one_of_not_mem_Ioo x hx)

/-- The original meridional section is nonzero exactly when its coefficient is
nonzero somewhere in the open physical height interval. -/
theorem meridionalOneForm_ne_zero_iff (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    D.meridionalOneForm r hr ≠ 0 ↔ ∃ v ∈ Ioo (-1 : ℝ) 1, r v ≠ 0 := by
  constructor
  · intro h
    by_contra hzero
    apply h
    apply (D.meridionalOneForm_eq_zero_iff r hr).2
    intro v hv
    by_contra hrv
    exact hzero ⟨v, hv, hrv⟩
  · rintro ⟨v, hv, hrv⟩ hz
    exact hrv ((D.meridionalOneForm_eq_zero_iff r hr).1 hz v hv)

/-- The original azimuthal section vanishes exactly when its coefficient
vanishes throughout the open physical height interval. -/
theorem azimuthalOneForm_eq_zero_iff (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) :
    D.azimuthalOneForm s hs = 0 ↔ ∀ v ∈ Ioo (-1 : ℝ) 1, s v = 0 := by
  constructor
  · intro h v hv
    let q : cylinderDomain := ⟨WithLp.toLp 2 ![v, 0], hv⟩
    let V : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
    have hev := D.azimuthalOneForm_cylinderMap_mfderiv s hs q V
    rw [h] at hev
    have hprod : warp D.a v * s v = 0 := by
      simpa [q, V] using hev.symm
    have hw : 0 < warp D.a v := D.cylinderMap_warp_pos q
    exact (mul_eq_zero.mp hprod).resolve_left hw.ne'
  · intro h
    apply DFunLike.ext
    intro x
    change D.azimuthalOneForm s hs x = 0
    by_cases hx : sphereHeight x ∈ Ioo (-1 : ℝ) 1
    · apply ContinuousMultilinearMap.ext
      intro slots
      change D.azimuthalOneForm s hs x slots = 0
      rw [azimuthalOneForm_apply, h _ hx, mul_zero, zero_mul]
    · exact D.azimuthalOneForm_eq_zero_at_pole s hs x
        (sphereHeight_sq_eq_one_of_not_mem_Ioo x hx)

/-- The original azimuthal section is nonzero exactly when its coefficient is
nonzero somewhere in the open physical height interval. -/
theorem azimuthalOneForm_ne_zero_iff (D : PoleData) (s : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ s) :
    D.azimuthalOneForm s hs ≠ 0 ↔ ∃ v ∈ Ioo (-1 : ℝ) 1, s v ≠ 0 := by
  constructor
  · intro h
    by_contra hzero
    apply h
    apply (D.azimuthalOneForm_eq_zero_iff s hs).2
    intro v hv
    by_contra hsv
    exact hzero ⟨v, hv, hsv⟩
  · rintro ⟨v, hv, hsv⟩ hz
    exact hsv ((D.azimuthalOneForm_eq_zero_iff s hs).1 hz v hv)

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
