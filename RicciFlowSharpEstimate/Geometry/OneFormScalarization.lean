/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipation
import RicciFlowSharpEstimate.Geometry.OneFormScalars
import RicciFlowSharpEstimate.Geometry.SurfaceTensorDerivativeDecomposition
import RicciFlowSharpEstimate.Geometry.OneFormSecondDerivativeNorm
import RicciFlowSharpEstimate.Geometry.SurfaceTensorIntegration

/-!
# Constructive scalarization of complete one-form dissipation

The actual curvature commutator and canonical integration by parts remove the
skew pairing of the second derivative. The remaining norm splits into the
derivatives of the Ahlfors part, trace and oriented curl of the original form.
Every integral is justified by smoothness and compactness.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
variable [IsManifold 𝓡₂ ∞ M] [T2Space M] [CompactSpace M]
variable [BoundarylessManifold 𝓡₂ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The original complete dissipation equals the Ahlfors energy plus the actual
trace and oriented-curl scalar energies on a closed surface. -/
theorem oneFormDissipation_scalarization (g : SmoothRiemannianMetric 𝓡₂ M)
    (Ω : TwoTensorSection (I := 𝓡₂) (M := M))
    (h : OneFormSection (I := 𝓡₂) (M := M))
    (hAlt : ∀ x v w, Ω x (vec2 v w) = -Ω x (vec2 w v))
    (hUnit : ∀ x, normSq0S g x 2 (Ω x) = 2) :
    oneFormDissipation g h =
      (∫ x, normSq0S g x 3 (metricNabla0S g (ahlforsPart g (metricNabla0S g h)) x)
        ∂(riemannianVolumeMeasure (I := 𝓡₂) (M := M) g)) +
      3 * (∫ x, (metricScalarAt g x / 2) *
          normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x)
        ∂(riemannianVolumeMeasure (I := 𝓡₂) (M := M) g)) +
      (1 / 2 : ℝ) *
        ((∫ x, normSq0S g x 1 (differential1FormFun (oneFormTrace g h) x) -
            (metricScalarAt g x / 2) * oneFormTrace g h x ^ 2
          ∂(riemannianVolumeMeasure (I := 𝓡₂) (M := M) g)) +
        ∫ x, normSq0S g x 1 (differential1FormFun (oneFormCurl g Ω h) x) -
            (metricScalarAt g x / 2) * oneFormCurl g Ω h x ^ 2
          ∂(riemannianVolumeMeasure (I := 𝓡₂) (M := M) g)) := by
  let μ := riemannianVolumeMeasure (I := 𝓡₂) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hInt {f : M → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  let K : M → ℝ := fun x => metricScalarAt g x / 2
  let τ := oneFormTrace g h
  let curlScalar := oneFormCurl g Ω h
  let S := metricNabla0S g h
  let A := ahlforsPart g S
  let B := metricNabla0S g S
  let L : M → ℝ := fun x => normSq0S g x 1 (roughLap0SField g h x)
  let Z : M → ℝ := fun x => K x ^ 2 * normSq0S g x 1 (h x)
  let N : M → ℝ := fun x => K x * normSq0S g x 2 (S x)
  let W : M → ℝ := fun x => K x * normSq0S g x 2 (A x)
  let F : M → ℝ := fun x => normSq0S g x 3 (B x)
  let G : M → ℝ := fun x => normSq0S g x 3 (metricNabla0S g A x)
  let U : M → ℝ := fun x => normSq0S g x 1 (differential1FormFun τ x)
  let V : M → ℝ := fun x => normSq0S g x 1 (differential1FormFun curlScalar x)
  let T : M → ℝ := fun x => K x * τ x ^ 2
  let O : M → ℝ := fun x => K x * curlScalar x ^ 2
  let C : M → ℝ := fun x => inner0S g x 3
    ((B x).domDomCongr (Equiv.swap (0 : Fin 3) 1)) (B x)
  have hK : Continuous K := ((metricScalar_smooth g).div_const 2).continuous
  have hτ := oneFormTrace_contMDiff g h
  have hω := oneFormCurl_contMDiff g Ω h
  have hL : Integrable L μ := hInt (normSq0S_smooth g (roughLap0SField g h)).continuous
  have hZ : Integrable Z μ := hInt ((hK.pow 2).mul (normSq0S_smooth g h).continuous)
  have hN : Integrable N μ := hInt (hK.mul (normSq0S_smooth g S).continuous)
  have hW : Integrable W μ := hInt (hK.mul (normSq0S_smooth g A).continuous)
  have hF : Integrable F μ := hInt (normSq0S_smooth g B).continuous
  have hG : Integrable G μ := hInt (normSq0S_smooth g (metricNabla0S g A)).continuous
  have hU : Integrable U μ := hInt (normSq0S_smooth g (duSec τ hτ)).continuous
  have hV : Integrable V μ := hInt (normSq0S_smooth g (duSec curlScalar hω)).continuous
  have hT : Integrable T μ := hInt (hK.mul (hτ.continuous.pow 2))
  have hO : Integrable O μ := hInt (hK.mul (hω.continuous.pow 2))
  have hskew (x : M) : F x - C x = Z x :=
    oneForm_secondDerivative_skew_pairing hdim g h x
  have hCeq : C = fun x => F x - Z x := by
    funext x
    linarith only [hskew x]
  have hC : Integrable C μ := by rw [hCeq]; exact hF.sub hZ
  have hFC : (∫ x, F x ∂μ) - (∫ x, C x ∂μ) = ∫ x, Z x ∂μ := by
    rw [← integral_sub hF hC]
    exact integral_congr_ae (Filter.Eventually.of_forall hskew)
  have hCW : (∫ x, C x ∂μ) = (∫ x, L x ∂μ) - 2 * ∫ x, W x ∂μ := by
    have hmix := integral_inner0S_gradSlotSwap hdim g S
    have heq : (fun x => metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x)) =
        fun x => 2 * W x := by
      funext x
      dsimp only [W, A, K]
      ring
    rw [heq, integral_const_mul] at hmix
    exact hmix
  have hFG (x : M) : F x = G x + (1 / 2 : ℝ) * (U x + V x) := by
    have hsplit := normSq0S_metricNabla0S_twoTensor_split hdim g S Ω hAlt hUnit x
    change F x = G x + (U x + V x) / 2 at hsplit
    linarith only [hsplit]
  have hFGint : (∫ x, F x ∂μ) = (∫ x, G x ∂μ) +
      (1 / 2 : ℝ) * ((∫ x, U x ∂μ) + ∫ x, V x ∂μ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hFG)]
    rw [integral_add (f := G) (g := fun x => (1 / 2 : ℝ) * (U x + V x))
      hG ((hU.add hV).const_mul (1 / 2)),
      integral_const_mul, integral_add hU hV]
  have hNW (x : M) : N x = W x + (1 / 2 : ℝ) * (T x + O x) := by
    have hsplit := normSq0S_twoTensor_eq_ahlforsPart_trace_curl
      hdim g S x (Ω x) (hAlt x) (hUnit x)
    have hm := congrArg (fun t : ℝ => K x * t) hsplit
    change K x * normSq0S g x 2 (S x) =
      K x * (normSq0S g x 2 (A x) + (τ x ^ 2 + curlScalar x ^ 2) / 2) at hm
    dsimp only [N, W, T, O]
    linarith only [hm]
  have hNWint : (∫ x, N x ∂μ) = (∫ x, W x ∂μ) +
      (1 / 2 : ℝ) * ((∫ x, T x ∂μ) + ∫ x, O x ∂μ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hNW)]
    rw [integral_add (f := W) (g := fun x => (1 / 2 : ℝ) * (T x + O x))
      hW ((hT.add hO).const_mul (1 / 2)),
      integral_const_mul, integral_add hT hO]
  have hQ : oneFormDissipation g h =
      (∫ x, L x ∂μ) + (∫ x, Z x ∂μ) - (∫ x, N x ∂μ) + 2 * ∫ x, W x ∂μ := by
    have hpoint (x : M) : oneFormDissipationDensity g h x = L x + Z x - N x + 2 * W x := by
      dsimp only [oneFormDissipationDensity, L, Z, N, W, K, S, A]
      ring
    change (∫ x, oneFormDissipationDensity g h x ∂μ) = _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_add (f := fun x => L x + Z x - N x) (g := fun x => 2 * W x)
        ((hL.add hZ).sub hN) (hW.const_mul 2),
      integral_sub (f := fun x => L x + Z x) (hL.add hZ) hN,
      integral_add hL hZ, integral_const_mul]
  change oneFormDissipation g h = (∫ x, G x ∂μ) + 3 * (∫ x, W x ∂μ) +
    (1 / 2 : ℝ) * ((∫ x, U x - T x ∂μ) + ∫ x, V x - O x ∂μ)
  rw [integral_sub hU hT, integral_sub hV hO]
  linarith only [hQ, hFC, hCW, hFGint, hNWint]

end RicciFlowSharpEstimate.Geometry
