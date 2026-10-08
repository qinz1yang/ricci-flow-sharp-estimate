# Geometric statement audit and remaining equality bridge

Status: **source inspection and unformalized research**. Historical filenames below refer to the owner-provided reference inventory. None of its geometric theorems has been accepted under the new pinned release. Newly derived estimates are explicit proof obligations.

## Actual geometric object and natural class

`BalancedRotationalSphereMetric.Data` (`BalancedRotationalSphereMetric.lean:42`) contains globally smooth real functions a,b,c, positivity of a and b on [-1,1], balance ∫v a(v)dv=0, and the exact pole-removal equations

    f(v) = 2 ∫_v^1 ξ a(ξ)dξ = (1-v²)b(v),
    a(v)²-b(v)² = (1-v²)c(v)                         on [-1,1].

Its metric is the actual smooth positive definite tensor on the standard unit two-sphere

    g = b(z) g_round + (c(z)/b(z)) dz⊗dz.

On the open cylinder this is g=(a²/f)dv²+f dθ². `Data.metric` is a `SmoothRiemannianMetric (𝓡 2) RotationalSphere`; `RotationalSphere` is the ordinary unit sphere in Euclidean three-space, not a replacement geometry.

The auxiliary b,c are produced from a: `exists_data_of_smooth_positive_balanced_profile_with_pole_values` (`SmoothBalancedRotationalSphereMetric.lean:128`) assumes `a : ℝ → ℝ`, `ContDiff ℝ ∞ a`, a>0 on [-1,1], and balance=0, and returns `∃ D : Data, D.a=a ∧ D.b(-1)=D.a(-1) ∧ D.b(1)=D.a(1)`. The simpler theorem at line 176 retains `D.a=a`. Proof: Hadamard factorization at ±1 twice, with the endpoint slopes forcing b(±1)=a(±1). No reflection symmetry is assumed.

Natural paper domain: a smooth on a neighborhood of [-1,1], positive there/on the closed interval, balanced; the Lean reference uses a globally smooth extension. If the new paper chooses neighborhood smoothness, prove the extension bridge instead of silently equating it with the stronger old input.

Nonvacuity witness: a=b=A>0, c=0 gives the round metric scaled by A; all tying equations hold. This is a source-level mathematical witness, not a newly compiled constructor.

The exact old public class (`RotationalConformalKillingSharpThreshold.lean:35`) is

    IsBalancedRotationalMetric g :=
      ∃ D : Data, ∃ Φ : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
        Diffeomorph.pullbackMetric D.metric Φ = g.

This quantifies over smooth diffeomorphic pullbacks of these actual metrics. It does not assert that every abstract effective smooth isometric circle action has this representation. Keep this class restriction unless an independent global classification/coordinate bridge is proved.

## Canonical derivatives and full dissipation

Use Q_g(h) as a prose abbreviation for `oneFormHodgeDissipationHalf g h (canonicalOneFormTwoJet g h).nabla (canonicalOneFormTwoJet g h).nabla2`. The first and second jets come from the genuine Levi-Civita connection (`CanonicalOneFormTwoJet.lean`); they are not free fields or hypotheses.

The actual four-term expression is

    Q_g(h) = ∫[ |roughLap h|² + K²|h|² − K|∇h|² + 2K|A h|² ] dμ_g,

where A h is the trace-free symmetric part of ∇h (the genuine Ahlfors operator). Do not replace this by the energy of just one component or a reduced functional without a producer equality. The geometric reference controls this static functional; it alone makes no coupled-flow existence claim.

## Exact meridional and zonal reduction

`zonalMeridionalOneForm D r hr` (`RotationalZonalOneForms.lean:41`) is exactly the smooth closed-sphere section

    M_D(r) = a(z) r(z) dz,        r : ℝ→ℝ, ContDiff ℝ ∞ r.

`zonalAzimuthalOneForm D r hr` (same file:338) is

    Z_D(r) = b(z)r(z)κ,
    κ = −y dx + x dy = (1−z²)dθ,

so Z_D(r)=f(z)r(z)dθ on the open cylinder. These definitions are smooth at both poles; merely writing dθ would not be a global producer.

`Data.momentHodgeState` and `...First` (`RotationalZonalHessianJet.lean:1161`) are

    H=f/a,
    H' = −2v − f a'/a².

The theorem at line 1170 proves the derivative on the entire closed physical interval. `zonalSquareValue` (`AxisymmetricSphereReduction.lean:25`) is exactly

    L_a r = H r'' + (H'−2v)r' − r.

`Data.zonalDissipationDensity` (`RotationalZonalDissipationIntegral.lean:52`) is exactly the proposed integrand

    H(L_a r)² + (H−2v²)r² + 2vHrr'.

The old theorem `Data.oneFormHodgeDissipationHalf_zonal_eq_two_pi_mul_integral` in that file states, for every D and every globally smooth r with its smoothness witness,

    Q_{D.metric}(M_D(r)) = 2π ∫_{−1}^1 [H(L_a r)²+(H−2v²)r²+2vHrr'] dv.

Its proof uses the exact canonical-jet pointwise formula on the open height cylinder, identifies `dμ_g=a(z)dμ_round`, discards only the two measure-zero poles, and applies round-height disintegration. There is no hidden endpoint term in J.

Independent convention check: with arclength t, φ=√f and dv/dt=√f/a, one has φ_t=−v and h=φr dt. The two diagonal components of ∇h are H r'−vr and −vr, hence |∇h|²=H²r'²−2vHrr'+2v²r² and 2|A h|²=H²r'². The rough-Laplacian term after multiplication by area density is H(L_a r)². The ±H²r'² terms cancel and leave the stated J. For a=A constant and r=1, H=1−v², J=4/3 and Q=8π/3; this fixes the factor 2π.

The complete zonal splitting has two ingredients: reflection orthogonality (`oneFormHodgeDissipationHalf_zonal_add_eq`, `RotationalZonalReflectionOrthogonality.lean:214`) and parallel Hodge rotation (`Data.oneFormHodgeDissipationHalf_zonalAzimuthal_eq_meridional`, `RotationalZonalHodgeStar.lean:148`). Together,

    Q(M_D(r)+Z_D(s)) = 2π(J_a[r]+J_a[s]).

The reflection used here is a meridian reflection θ↦−θ, available for every such metric. It is not equatorial reflection v↦−v.

`exists_smooth_zonal_decomposition_of_rotationInvariant` (`RotationalInvariantOneFormClassification.lean:3170`) takes the genuine condition `∀ z : Circle, circleOneFormPullback D z h = h` and returns globally smooth r,s and the exact section equality h=M_D(r)+Z_D(s). Its load-bearing smooth pole classification uses stereographic radial/tangential covector factorization; this producer cannot be replaced by an arbitrary coefficient package.

## Genuine Haar splitting and old remainder theorem

`oneFormRotationalAverage_apply_eq_integral_pullback` (`SmoothOneFormRotationalAverage.lean:558`) pins the producer P_D h by the pointwise equation

    (P_D h)_x(V) = (2π)⁻¹ ∫_0^{2π} (R_θ^*h)_x(V)dθ.

This is the actual circle action on the sphere, including the derivative in the covector pullback. `oneFormRotationalRemainder D h` is exactly h−P_D h (line 867). Smoothness, linearity and idempotence are proved for this producer.

`canonicalOneFormHodgeDissipationHalf_rotationalAverage_split` (`RotationalHaarDissipationProjection.lean:1906`) says, for every D and smooth one-form h,

    Q_D(h) = Q_D(P_D h)+Q_D(h−P_D h).

The proof is self-adjointness of this Haar projection for the full canonical four-term polarization, using genuine isometric pullback naturality and averaged canonical jets; not merely L² orthogonality of h.

`oneFormHodgeDissipationHalf_rotationalRemainder_nonneg` (`RotationalHaarRemainderNonnegative.lean:44`) says Q_D(h−P_D h)≥0 for every D,h, with no pinching hypothesis. Its proof produces the oriented trace/curl scalarization from the canonical first/second jets; proves K≥0 from K=1/a; uses trace/curl Haar intertwining and the two scalar estimates ∫Kτ²≤∫|dτ|² and ∫Kω²≤∫|dω|²; and uses the nonnegative Ahlfors terms.

This old theorem has no equality conclusion. Its hypothesis set does not contain nonzero h or a strict scalar gap. It cannot justify full CK strictness just from strictness of constant probes.

## Old CK statements and exact missing smooth-equality theorem

`rotationInvariant_ahlfors_eq_zero_iff_exists_constant_zonal_decomposition` (`RotationalConformalKilling.lean:484`) assumes the actual rotation invariance of h and asserts

    A h = 0 at every point  ↔  ∃ c d : ℝ, h=M_D(c)+Z_D(d).

`exists_constant_zonal_decomposition_rotationalAverage_of_ahlfors_eq_zero` (line 388) gives the same exact section representation for P_D h when h is any smooth CK one-form. It proves Haar averaging preserves CK. It does not classify the full nonzonal CK space.

`Data.oneFormHodgeDissipationHalf_nonneg_of_conformalKilling_profileRatio_le` (`RotationalConformalKillingSharpThreshold.lean:42`) takes D, `profileRatio D.unitReciprocalCurvatureProfile ≤ pureRotationCriticalRatio`, h, and A h=0, then proves Q_D(h)≥0 by the constant zonal decomposition and the unconditional Haar remainder theorem.

`oneFormHodgeDissipationHalf_nonneg_of_rotational_conformalKilling_pinching` (line 65) takes a genuine g, `IsBalancedRotationalMetric g`, smooth h, A_g h=0, kmin>0, pointwise kmin≤K_g≤kmax, and kmax/kmin≤C_CK. It concludes Q_g(h)≥0. Pullback naturality transports both CK and the full canonical Q; no orientation-preserving assumption is imposed on Φ.

The old supercritical theorem at line 110 quantifies `∀ C>C_CK, ∃ g` in this class, `∃ h` smooth CK, and `∃ kmin kmax` with kmin>0, pointwise curvature bounds, kmax/kmin<C, and Q_g(h)<0. Its constructed h is exactly M_D(1) for a smooth produced D. `exists_geometric_constantProbe_counterexample_ratio_lt` (`PureRotationConstantProbeGeometric.lean:169`) ties the actual D and canonical one-form to negative geometric Q. Negative Q itself certifies that h is nonzero; a natural corollary may state this explicitly.

The old closed-form threshold theorem is obtained from this safe endpoint and these genuine supercritical witnesses. Its source is not a new release certificate.

For the requested full smooth equality conclusion the additional natural target is:

    For every D and smooth h,
    Q_D(h−P_D h)=0  ↔  h−P_D h=0.

A sufficient weaker target restricts h to CK, but the unrestricted zero-Haar equality theorem is the natural reusable statement and appears mathematically accessible. Coupled with strictness of nonzero constant probes for smooth profiles at ratio≤C_CK, it gives

    IsBalancedRotationalMetric g, A_g h=0, ratio≤C_CK
      ⇒ [Q_g(h)=0 ↔ h=0].

The nonzero-form hypothesis or an explicit iff is mandatory: h=0 always attains zero. This statement is CK-only; it says nothing about smooth attainment at the unrestricted threshold.

## Concrete source-only route to the missing equality bridge

The old scalar route uses `WeightedPiconePolarInterval.integral_sin_mul_sq_le_integral_weightedEnergy`, proved by integrating a two-ended pointwise bound. It retains no coercive remainder. A direct exact completion supplies one.

Let s∈[0,π] be polar angle, W(s)=sin(s)b(cos s)/a(cos s)>0 in the interior. For a smooth zero-angular-mean scalar u on the sphere, each y(s)=u(s,θ) vanishes at both poles. The pointwise identity is

    W y'²+y²/W−sin(s)y²
      = (W y'−cos(s)y)²/W + sin²(s)y²/W + (cos(s)y²)'.

Integrate: the endpoint term is zero. Angular Wirtinger replaces ∫y²/W by ∫u_θ²/W. Since sin²/W=sin·a/b, conversion back to geometric area yields the stronger natural scalar estimate

    ∫ (|du|²_g−K u²)dμ_g ≥ ∫ u²/b(z)dμ_g.             (S)

This is a newly derived research proof route, NOT an old Lean theorem. Integrability can reuse the old `piconeDensity_scalarRemainder_integrable_prod`: the square is bounded by twice each radial/reciprocal-weight energy term, and the cross derivative is integrable. The only extra coefficient 1/b is smooth and positive on the compact sphere. This also identifies the usual positive comparison ground state √f on the open cylinder.

The inspected scalarization proof has the exact identity

    Q(h) = ||∇A h||²_{L²}+3∫K|A h|²dμ
      + 1/2[ ∫(|dτ|²−Kτ²)dμ + ∫(|dω|²−Kω²)dμ ].

For a zero-Haar form, τ and ω have zero scalar Haar mean. With (S), equality Q=0 forces A h=0, τ=0, ω=0 (positive weights and continuous integrands), hence ∇h=0 by the pointwise spin decomposition. The canonical second derivative is then zero; substituting into the original Q gives ∫K²|h|²=0, so h=0. This avoids an unproved harmonic-one-form vanishing theorem, although a native Bochner vanishing theorem would also finish. Every displayed step needs genuine Lean evidence before inclusion as an established paper result.

## Smooth nonattainment and the pair functional bridge

For a positive bounded profile a with m≤a≤M, use k(v)=log(M/a(v)), not log a(v). Then exp(k(v)−k(s))=a(s)/a(v), and

    ∫_0^1 H(v)dv = I(k).

The southern moment is I(k_−), k_−(v)=log(M/a(−v)), by balance; reflection symmetry is not assumed. The exact constant-probe identity from `RotationalConstantProbeSharpBound.lean:82` is

    J_a[c] = [2(I(k_+)+I(k_−))−4/3] c².

Thus Q(M_D(c)+Z_D(d))=2π[2(I(k_+)+I(k_−))−4/3](c²+d²). This pins the sign and normalization for all future stability/nonattainment statements.

Once the proposed all-cap optimizer and uniqueness are proved: for C>1, α<β and its free-arc logarithmic derivative is

    k_*'(v)=1/(2v)+sqrt(v)/α^(3/2),

which equals 3/(2α)>0 at α from the right while the lower obstacle derivative is zero; at β it is also positive while the upper obstacle derivative is zero. The optimizer is continuous, not C¹. At C=1 the free arc collapses and k_*=0 is smooth, so the derivative-jump conclusion must explicitly exclude C=1.

At C=C_CK, equality I(k_±)=1/3 would force the nonsmooth optimizer, impossible for the smooth positive a; hence the zonal coefficient is strictly positive. Below C_CK, the all-cap optimal value gives strictness directly. This proves only the zonal part until the zero-Haar equality theorem above is closed.

Do not call the continuous optimizer a smooth geometric endpoint witness. A correct full conclusion is: the CK cap is sharp through smooth supercritical negative witnesses below every larger cap, while at the safe endpoint every smooth nonzero CK form has strictly positive Q (after proving the remainder equality bridge). An approximating smooth sequence requires an exact box/balance-preserving producer and convergence of the actual functional. For constant probes the latter depends only on C⁰ profile data; general probes depend on a' and require stronger recovery.

## Area-coordinate correction

The old moment coordinate is x₀(v)=∫_0^v a. Its endpoints are not 0 by definition. If x=x₀(v)−x₀(−1) is measured from the south pole, then dx=a dv, f_x=−2v, f_xx=−2/a=−2K, f(0)=0, f_x(0)=2. Therefore

    f_K(x)=2x−2∫_0^x(x−s)K(s)ds.

The affine term and minus sign are necessary. On [0,L] the two north-pole conditions are equivalent to ∫_0^L K=2 and ∫_0^L sK(s)ds=L. Any area-coordinate recovery must preserve the actual interval and these exact moments. The centered coordinate x₀ has a different affine initialization; do not transplant the south-pole formula without the shift.

## Finite bridge obligations and dependency order

1. Natural smooth balanced profile producer → exact metric, pole factors, K=1/a, volume=a·round volume, genuine axis action. Keep a=A round witness and the tying equation D.a=a.
2. Canonical section jets and isometric/diffeomorphic naturality → actual smooth Haar average, normalized pullback integral, idempotence, jet intertwining, full four-term polarized split.
3. Actual global M_D/Z_D producers → canonical pointwise calculation → 2πJ normalization; fixed-point smooth pole classification plus meridian-reflection orthogonality and Hodge rotation → full zonal reduction.
4. Scalar zero-Haar producer → angular Wirtinger + polar completion with positive 1/b remainder (S) → trace/curl intertwining + native scalarization → nonnegative Haar remainder and equality iff zero. New equality branch; keep it open until native evidence exists.
5. Native all-cap variational value/uniqueness/stability → correct k=log(M/a) hemisphere bridge → smooth constant-probe strictness at critical ratio and independently smooth supercritical recovery.
6. CK Haar preservation + constant zonal classification + (4) + (5) → full CK nonnegativity, exact smooth equality iff h=0, and smooth geometric counterexamples below every supercritical cap; transport all objects through the same Φ.

No arbitrary effective-circle-action enlargement, no smooth unrestricted endpoint attainment, and no actual coupled Ricci-Hodge evolution follows from these source statements. These remain separate obligations only if selected into scope.
