/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothParity

/-!
# Smooth rotation-equivariant covectors on the plane

We identify a Euclidean covector with its two coefficients.  Pullback
invariance of the covector is then exactly rotation equivariance of this
coefficient pair.

Adapted from Ziyang Qin's pinned `SmoothRotationalCovectorPlane.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set
open scoped ContDiff


/-- Counterclockwise rotation of a point by the matrix with entries
`c = cos θ`, `s = sin θ`. -/
def planeRotate (c s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (c * p.1 - s * p.2, s * p.1 + c * p.2)

/-- Equivariance condition for the coefficient pair of a
rotation-invariant Euclidean covector. -/
def IsRotationCovectorPair
    (P Q : ℝ × ℝ → ℝ) : Prop :=
  ∀ (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∀ p : ℝ × ℝ,
      P (planeRotate c s p) =
          c * P p - s * Q p ∧
        Q (planeRotate c s p) =
          s * P p + c * Q p

/-- A smooth rotation-equivariant covector pair has smooth radial and
tangential coefficients depending only on squared radius. -/
theorem exists_smooth_radial_tangential_coefficients
    (P Q : ℝ × ℝ → ℝ)
    (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hcov : IsRotationCovectorPair P Q) :
    ∃ A B : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧
      ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ x y : ℝ,
        P (x, y) =
            x * A (x ^ 2 + y ^ 2) -
              y * B (x ^ 2 + y ^ 2) ∧
          Q (x, y) =
            y * A (x ^ 2 + y ^ 2) +
              x * B (x ^ 2 + y ^ 2) := by
  let p : ℝ → ℝ := fun t => P (t, 0)
  let q : ℝ → ℝ := fun t => Q (t, 0)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := by
    exact hP.comp (contDiff_id.prodMk contDiff_const)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by
    exact hQ.comp (contDiff_id.prodMk contDiff_const)
  have hpOdd : Function.Odd p := by
    intro t
    have h := hcov (-1) 0 (by norm_num) (t, 0)
    simpa [p, planeRotate] using h.1
  have hqOdd : Function.Odd q := by
    intro t
    have h := hcov (-1) 0 (by norm_num) (t, 0)
    simpa [q, planeRotate] using h.2
  obtain ⟨A, hA, hpFactor⟩ :=
    exists_contDiff_mul_comp_sq_of_odd p hp hpOdd
  obtain ⟨B, hB, hqFactor⟩ :=
    exists_contDiff_mul_comp_sq_of_odd q hq hqOdd
  refine ⟨A, B, hA, hB, ?_⟩
  intro x y
  let r : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
  by_cases hrzero : r = 0
  · have hsumNonpos : x ^ 2 + y ^ 2 ≤ 0 := by
      exact Real.sqrt_eq_zero'.mp hrzero
    have hxzero : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hyzero : y = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    subst x
    subst y
    have hp0 := hpFactor 0
    have hq0 := hqFactor 0
    simp only [p, q, zero_mul] at hp0 hq0
    constructor
    · simpa using hp0
    · simpa using hq0
  · have hsumPos : 0 < x ^ 2 + y ^ 2 := by
      by_contra h
      exact hrzero
        (Real.sqrt_eq_zero_of_nonpos (le_of_not_gt h))
    have hrpos : 0 < r :=
      Real.sqrt_pos.2 hsumPos
    have hrsq : r ^ 2 = x ^ 2 + y ^ 2 := by
      exact Real.sq_sqrt hsumPos.le
    let c : ℝ := x / r
    let s : ℝ := y / r
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp only [c, s]
      field_simp
      nlinarith
    have hrot : planeRotate c s (r, 0) = (x, y) := by
      apply Prod.ext
      · dsimp only [planeRotate, c, s]
        simp [hrzero]
      · dsimp only [planeRotate, c, s]
        simp [hrzero]
    have h := hcov c s hcs (r, 0)
    rw [hrot] at h
    have hpR := hpFactor r
    have hqR := hqFactor r
    simp only [p, q] at hpR hqR
    rw [hpR, hqR, hrsq] at h
    dsimp only [c, s] at h
    constructor
    · calc
        P (x, y) =
            (x / r) *
                (r * A (x ^ 2 + y ^ 2)) -
              (y / r) *
                (r * B (x ^ 2 + y ^ 2)) := h.1
        _ =
            x * A (x ^ 2 + y ^ 2) -
              y * B (x ^ 2 + y ^ 2) := by
          field_simp
    · calc
        Q (x, y) =
            (y / r) *
                (r * A (x ^ 2 + y ^ 2)) +
              (x / r) *
                (r * B (x ^ 2 + y ^ 2)) := h.2
        _ =
            y * A (x ^ 2 + y ^ 2) +
              x * B (x ^ 2 + y ^ 2) := by
          field_simp

end RicciFlowSharpEstimate.Analysis
