# Phase II: the unrestricted rotational threshold

Phase I is **COMPLETE**, accepted after rounds 0–16 at
`2bda267ca0a4bd965411af36b2c89dde4c78f7c7` and finalized at
`721fd81b76a3c841389761fbe55ce917e0926a44`. Its paper and evidence are preserved.
Phase II is **OPEN**. Its goal is to determine `C_rot` for all smooth one-forms
on the original represented rotational metric class, with a determining
characterization, justified selection, a universal lower bound, sharp smooth
counterexamples above it, and the correct endpoint scope. The results below
are variational prerequisites, not a threshold characterization.

## Round 0: complete-action variation

Let `K,r : ℝ → ℝ` be globally smooth, and impose the two normalized moments

\[
 \int_0^1K=2,\qquad \int_0^1xK=1.
\]
Use the **existing** area primitives and full six-entry action:

\[
 f(x)=2x-2\int_0^x(x-t)K(t)\,dt,\qquad
 f_1(x)=2-2\int_0^xK(t)\,dt,
\]
\[
 L_Kr=fr''+2f_1r'-Kr,
\]
\[
 A_K(r)=\int_0^1
 \left[f(L_Kr)^2-Kf_1r(fr'+f_1r/2)+K^2fr^2\right]dx.
\]
The accepted primitive calculus gives `f'=f₁`, `f₁'=-2K`,
`f(0)=f(1)=0`, and `f₁(0)=2`, `f₁(1)=-2`.

The new native factorization is

\[
 A_K(r)=\int_0^1\left[f(L_Kr)^2+\frac12ff_1K'r^2\right]dx. \tag{1}
\]
Indeed, the original density minus the right-hand density is the actual
derivative of `-K f f₁ r²/2`. Its endpoint values vanish because `f` vanishes,
without a condition on either endpoint value or derivative of `r`.
All terms are continuous and integrable. Neither (1) nor the Green identity
below requires positive curvature; positivity enters the normalization and
stationarity converse.

The actual Green flux is

\[
 G_K(r,s)=f^2(r's-rs'),\qquad
 G_K(r,s)'=f(L_Kr)s-fr(L_Ks).
\]
It vanishes at both endpoints for **all** smooth probes. Thus `L_K` is symmetric
for the weighted pairing `∫f r s`. Applying this identity to (1) gives

\[
 E_Kr=L_K(L_Kr)+\frac12f_1K'r,\qquad
 A_K(r)=\int_0^1frE_Kr. \tag{2}
\]
The exact variation, with the actual derivatives of `r+ts`, is

\[
 A_K(r+ts)=A_K(r)+2t\int_0^1fsE_Kr+t^2A_K(s). \tag{3}
\]
Consequently its parameter derivative at zero is `2∫f s E_Kr`.
This retains the full curvature potential; replacing the action by its leading
square alone would lose a term.

For `K>0` on `[0,1]`, the accepted concavity argument gives `f>0` in `(0,1)`.
The new stationarity theorem proves the equivalence

\[
 \left[\frac{d}{dt}\bigg|_{t=0}A_K(r+ts)=0
       \text{ for every globally smooth }s\right]
 \quad\Longleftrightarrow\quad E_Kr=0\text{ on }[0,1]. \tag{4}
\]
For the forward implication, take the legitimate smooth test `s=E_Kr`.
Its weighted-square integral is zero; continuity and positive interior weight
force `E_Kr=0` in the interior and then at the endpoints. This is an equivalence
for a **supplied smooth probe**, not an existence theorem for a nonzero kernel
or a proof that a joint optimizer exists.

Writing `q=L_Kr`, the endpoint values in (4) give

\[
 4q'(0)-K(0)q(0)+K'(0)r(0)=0,\qquad
 -4q'(1)-K(1)q(1)-K'(1)r(1)=0. \tag{5}
\]
These are consequences of the smooth equation. They are not asserted to be a
sufficient boundary-domain description for arbitrary singular solutions of the
fourth-order ODE. The leading coefficient of `E_K` is `f²`, which degenerates
at both poles; that distinction matters for any later spectral or compactness
argument.

If `r` is nonzero somewhere in `(0,1)`, the new positivity theorem gives
`m=∫f r²>0`. The explicit positive rescaling `c=1/√m` satisfies

\[
 \int_0^1f(cr)^2=1,\qquad A_K(cr)=c^2A_K(r). \tag{6}
\]
This establishes a legitimate scalar normalization and preserves action sign
and zero action. It does not manufacture a nonzero critical probe. At this
Round 0 checkpoint, metric-scale normalization and the completed
operator domain were separate obligations. Round 2 below supplies the exhaustive
smooth metric/probe normalization; a completed singular operator domain remains open.

## Original objects and pole scope

The existing `RotationalOneForms` producer permits every globally smooth height
probe, and `RotationalInvariantClassification` supplies globally smooth probes
for every original invariant smooth form. The forms vanish at the poles because
the geometric covectors vanish there; the scalar probes need not vanish.
The accepted smooth area inverse and `AreaGeometricRealization` construct actual
original metric/profile/probe data with the closed-interval coordinate equations
and actual first and second derivative laws. No singular angular coordinate or
independently supplied jets occur in the new packet.

The new `AreaVariationGeometry` consumers explicitly retain the same `D.metric`,
`D.meridionalOneForm`, height primitive, and physical equations

\[
 D.a(V_K(x))=1/K(x),\quad R(V_K(x))=r(x),\quad S(V_K(x))=s(x)
 \qquad(0\leq x\leq1).
\]
They prove the original dissipation version of (2), and

\[
 \frac{d}{dt}\bigg|_{t=0}Q_{g_D}(M_D(R+tS))
   =4\pi\int_0^1fsE_Kr. \tag{7}
\]
The metric is fixed throughout this variation. These are consumers of the
accepted tying equations, whose producer remains available; they do not rename
a scalar action as a geometric object.
The accepted Haar reduction and nonnegative nonzonal remainder remain unchanged.
No new universal positivity claim, extension to all positively curved surfaces,
or exhaustive normalized-area parametrization theorem is asserted by the Round 0
packet. Round 2 below supplies the latter smooth reduction.

## Native declaration map and evidence

All names below are in `RicciFlowSharpEstimate.Geometry.AreaProfile`.

| Result | Canonical source and declaration |
|---|---|
| Actual operator and smoothness | `Geometry/AreaActionFactorization.lean`: `meridionalOperator`, `meridionalOperator_contDiff` |
| Complete factorization (1) | Same module: `meridionalAction_eq_square_potential`; private actual flux derivative |
| Green derivative and automatic pole flux | `Geometry/AreaActionVariation.lean`: `meridionalGreenFlux_hasDerivAt`, `meridionalGreenFlux_endpoints`, `integral_warp_mul_operator_mul` |
| Euler operator, polarization and (2) | Same module: `meridionalJacobiOperator`, `meridionalJacobiOperator_contDiff`, `integral_meridionalOperator_pair_eq_jacobi`, `meridionalAction_eq_integral_jacobi` |
| Actual affine derivatives and (3) | Same module: `meridionalOperator_add_mul`, `meridionalAction_add_mul`, `meridionalAction_hasDerivAt` |
| Smooth stationarity (4) and endpoint values (5) | Same module: `meridionalAction_stationary_iff`, `meridionalJacobiOperator_zero`, `meridionalJacobiOperator_one` |
| Nonzero normalization and homogeneity (6) | Same module: `integral_warp_mul_sq_pos`, `meridionalAction_const_mul`, `exists_normalized_area_probe` |
| Original metric/form pairing and variation (7) | `Geometry/AreaVariationGeometry.lean`: `oneFormDissipation_eq_integral_jacobi_of_profile_probe`, `oneFormDissipation_meridional_hasDerivAt` |

The [source-bound Round 0 native gate](../evidence/phase2-round-0-final/receipt.json)
passed: three new modules were freshly elaborated; 149 unchanged phase-I source
elaborations were reused with verified hashes. The root aggregate, unsuppressed
declaration linters, exact signatures and actual transitive axiom closure passed
for 152 modules and 2,449 defining-module declarations, including 801 private
ones. Only `propext`, `Classical.choice` and `Quot.sound` occur in the checked
closures. The new packet has 19 public theorems and three actual operator/flux
definitions. The Round 0 outer review accepted this bounded packet at `cea7baa`; full phase-II
acceptance remains open. These notes are
separate from the accepted phase-I manuscript; its TeX and PDF are unchanged.

## Historical tools: bounded audit outcome

The supplied frozen historical tree does not contain
`ConnectionGlobalCalibrationRigidity.lean` or `ConnectionProjectedSFSRigidity.lean`.
Their exact statements and dependency closures remain unassessed. Missing files
are an evidence limitation, not a refutation of their contents. No old theorem
is imported into the new native packet.

The available downstream sources contain substantive results, with explicit
remaining premises:

- `ConnectionSmoothMeridianGeometricRealization.ClosedSphereZonalSafe` states
  universal nonnegativity of the original smooth meridional action in a curvature
  box. Its recovery consumer transports that supplied safety statement through
  genuine smooth geometric realization.
- `ConnectionPhysicalFiniteMeridianAssembly.CoordinatizedFiniteInterfaceTerminalPolarAssembly.action_glue` proves additive action
  from actual transported jets and interval telescoping. The final activity
  consumer still takes sphere safety, a coordinatized assembly for the relevant
  histories, an opposite completion and a zero-action pair. It does not produce
  a critical optimizer or global safety from a numerical branch.
- `FullBalancedBernsteinThreshold` has an endpoint-safety argument for its
  exhaustive negative-witness threshold. The final connection-identification
  theorem in `RotationalAllOneFormThreshold` requires candidate safety and
  failure of every larger cap. Equating that threshold with a candidate ratio
  under those assumptions does not evaluate the ratio.
- `ConnectionProjectedFeedback` proves a pointwise clamp maximization law.
  `ConnectionPhysicalHamiltonianReduction` needs strict physical concavity and
  actual coefficient/maximization identities. On its positive branch, the
  inspected strict-concavity condition is equivalent to `costate_N < -R/2`.
  The clamp algebra does not supply that sign or a fixed number of contacts.
- The available Bregman/Picone and active-costate leaves require their stated
  sign, zero-defect or endpoint-variation realization hypotheses. They are
  useful conditional tools, not an established global original-action calibration.

This is source-level research inventory. The historical manifest labels those
bytes unverified; current phase-I receipts are not compiler or transitive-axiom
evidence for the historical tree. The new packet uses only current accepted
native dependencies.

## Round 1: actual curvature variation and normalized conditions

The core curvature derivative needs continuous `K,ξ` and a globally smooth fixed
probe `r`. For original smooth variations, take both `K` and `ξ` globally smooth.
No derivative of the curvature is used in this calculation. Put

\[
 K_t=K+t\xi,\quad b=f_1,\quad p=r',\quad z=r'',\quad q=fr''+2br'-Kr.
\]
The actual affine primitive laws are

\[
 f_{K_t}=f+t\delta f,\quad b_{K_t}=b+t\delta b,\qquad
 \delta f(x)=-2\int_0^x(x-u)\xi(u)\,du,\quad
 \delta b(x)=-2\int_0^x\xi(u)\,du.
\]
The fixed affine term `2x` in the warp is retained. The new complete-density
coefficients, evaluated at the original `K,r`, are

\[
 \begin{aligned}
 \alpha&=q^2+2fqz-Kbrp+K^2r^2,\\
 \beta&=4fqp-Kr(fp+br),\\
 \gamma&=-2fqr-br(fp+br/2)+2Kfr^2.
 \end{aligned}
\]
An exact cubic expansion in `t`, followed by integration of continuous
coefficients, proves the actual parameter derivative

\[
 \frac{d}{dt}\bigg|_0 A_{K_t}(r)
 =\int_0^1(\alpha\delta f+\beta\delta b+\gamma\xi). \tag{8}
\]
This is differentiation of the existing complete action, not an assumed
first-variation field. The proof supplies every integrability condition.

For continuous coefficients the new generic Volterra pairing theorems transfer
prefix primitives to tail primitives. They are proved from actual FTC derivatives
and integration by parts, including either orientation of the endpoints.
Applying both kernel identities to (8) gives

\[
 \sigma(u)=\gamma(u)-2\int_u^1[(x-u)\alpha(x)+\beta(x)]\,dx,
 \qquad \delta A=\int_0^1\sigma(u)\xi(u)\,du. \tag{9}
\]
The switching density is continuous. Equation (9) supplies neither an obstacle
sign nor a count of contacts.

The two constraints on the direction,
`∫ξ=0` and `∫xξ=0`, preserve the original two curvature moments **exactly for
every parameter**. Both warp/slope variations vanish at both endpoints under
these constraints. Positivity of a continuous curvature on the compact physical
interval persists for all sufficiently small parameters of either sign.
A strict interior box has the same property. More generally, a direction whose
closed support in the physical interval lies strictly between the obstacles is
feasible for both signs, even if the original curvature touches an obstacle
elsewhere. The use of closed support supplies a uniform margin. Weak signs only
at contact points are not used as a substitute for a feasible neighborhood.
A segment `K+t(G−K)`, `0≤t≤1`, between two curvatures in the same closed box and
with the same normalized moments is genuinely one-sided feasible.

The normalized functional must account for the geometry dependence of the mass:

\[
 m(K,r)=\int_0^1f_Kr^2,\qquad
 \delta m=\int_0^1\delta f\,r^2.
\]
The new `normalizedProbe` is literally `r/√m`, and for `m>0` its mass is one.
For smooth normalized-moment data its complete action is the actual quotient
`\mathcal R(K,r)=A_K(r)/m(K,r)`.
For any real `μ`, define the corrected switching density

\[
 \sigma_\mu(u)=\sigma(u)+2\mu\int_u^1(x-u)r(x)^2\,dx.
\]
Native differentiation proves

\[
 \delta\bigl(A-\mu(m-1)\bigr)=\int_0^1\sigma_\mu\xi,
 \qquad
 \delta\mathcal R=\frac1m\int_0^1\sigma_{\mathcal R}\xi. \tag{10}
\]
Thus the mass correction is equivalent to replacing `α` by `α−μr²` in the
switching calculation. An arbitrary `μ` in the algebraic first identity is not
a claim that a Lagrange multiplier has been extracted from an optimizer.
The second identity fixes its coefficient to the actual Rayleigh quotient.

For smooth zero-moment curvature directions and positive initial mass, the
literal normalized curvature path has positive mass, unit normalized mass and
complete action equal to the quotient throughout a neighborhood of zero.
Consequently (10) is also the derivative of
`A_{K_t}(normalizedProbe K_t r)`. Local minima of these two scalar parameter
functions on any specified feasible parameter set are natively equivalent.
This proves the normalization bridge for this variation; it is distinct from
T6's exhaustive original-metric normalization.

For probe variations the actual quotient derivative is

\[
 \frac{d}{dt}\bigg|_0\mathcal R(K,r+ts)
 =\frac2m\int_0^1fs\,[E_Kr-\mathcal R(K,r)r]. \tag{11}
\]
With positive curvature, smooth data, both moments and positive mass, stationarity
under every smooth probe direction is equivalent to

\[
 E_Kr=\mathcal R(K,r)r\quad\text{on }[0,1]. \tag{12}
\]
The proof tests with the actual smooth residual and uses positive weighted mass
and endpoint continuity. At unit mass its eigenvalue is `A_K(r)`; a zero-mode
conclusion additionally requires zero action. A local minimum of the **literal
normalized-probe action** along every smooth probe direction implies (12).
No nonzero eigenfunction or optimizing pair is constructed.

The feasible parameter set used by the new curvature optimality consumers is
explicit: the same affine curvature must satisfy the box and both exact moments.
For a supplied `IsLocalMinOn` of the quotient on that set, a segment to any other
admissible curvature `G` gives

\[
 \int_0^1\sigma_{\mathcal R}(G-K)\geq0. \tag{13}
\]
For a zero-moment direction with closed support in the free region, the pairing
is zero, because both parameter signs are feasible. Strict interior box data
are a separate immediate consumer. These are justified directional necessary
conditions. They do not assert a joint minimizer, moment multipliers, global
sufficiency, principal-sheet signs, symmetry or finite contact structure.

### Round 1 native map

Area names below have prefix `RicciFlowSharpEstimate.Geometry.AreaProfile`.
Generic analysis names have the prefix indicated in the table.

| Result | Canonical declarations |
|---|---|
| Oriented primitive pairing | `Analysis.VolterraPairing.integral_mul_primitive_eq`, `integral_mul_kernel_eq` in `Analysis/VolterraPairing.lean` |
| Actual affine primitives and moments | `warp_add_mul`, `warpSlope_add_mul`, `warpVariation_hasDerivAt`, `warpSlopeVariation_hasDerivAt`, `curvature_moments_add_mul`, `curvature_variation_endpoints` in `Geometry/AreaCurvaturePrimitives.lean` |
| Complete density derivative (8) | Actual coefficient definitions and `meridionalAction_curvature_hasDerivAt` in `Geometry/AreaCurvatureVariation.lean` |
| Switching pairing (9) | `curvatureSwitchingDensity_continuous`, `curvatureFirstVariation_eq_integral_switching`, `meridionalAction_curvature_hasDerivAt_switching` in the same module |
| Probe mass, quotient and eigen-equation (11)–(12) | `probeMass_add_mul`, `probeMass_hasDerivAt`, `rayleighQuotient_hasDerivAt`, `rayleighQuotient_stationary_iff`, its unit-mass/zero-action specializations in `Geometry/AreaProbeRayleigh.lean` |
| Literal normalized probe | `probeMass_normalizedProbe`, `meridionalAction_normalizedProbe`, `normalized_probe_action_hasDerivAt`, `normalized_probe_euler_eq_of_isLocalMin` in the same module |
| Curvature mass correction (10) | `probeMass_curvature_add_mul`, `probeMass_curvature_hasDerivAt`, `action_sub_mass_curvature_hasDerivAt`, `rayleighQuotient_curvature_hasDerivAt` in `Geometry/AreaCurvatureVariation.lean` |
| Literal normalized curvature path | `normalized_curvature_action_hasDerivAt`, `eventually_normalized_curvature_variation`, `isLocalMinOn_normalized_curvature_iff` in the same module |
| Actual feasible neighborhoods/segments | The four compact-set and scalar interval theorems in `Analysis/AffineIntervalVariation.lean` |
| Constrained necessary conditions (13) | `Icc_subset_curvatureParameters_segment`, `curvatureParameters_mem_nhds_of_interior`, `curvatureParameters_mem_nhds_of_free_support`, `curvature_pairing_nonneg_of_isLocalMinOn_segment`, both zero-pairing consumers in `Geometry/AreaCurvatureOptimality.lean` |

The [Round 1 native gate](../evidence/phase2-round-1/receipt.json) passes for all
158 modules. It freshly elaborates the six new modules, reuses 152 unchanged
accepted source elaborations, and checks the root, unsuppressed declaration
linters, 956 signature queries and actual transitive axiom closures for 2,542
declarations, including 812 private declarations. Only the three permitted
foundational axioms occur. Its one fresh independent outer review passed at
`38bdb3139c7b57581649f9500b6f6dfd032c4a59`.
The accepted Round 0 source bytes and Phase-I paper remain unchanged.

The historical reconstructed first-variation declarations and their density and
primitive reconstruction equations were inspected as research evidence. The new
proof differentiates the current corrected primitives directly by exact cubic
expansion; no historical theorem, continuous-map reconstruction package or old
native certificate is imported. The available historical `C_FB` endpoint-safety
results remain substantive source evidence, as the Round 0 review records, but
still do not identify the unrestricted sharp number.

## Round 2: exhaustive normalization of original competitors

Start with arbitrary original `D : RotationalProfile.PoleData`, not prescribed
normalized curvature or a unit probe. Write `a=D.a`, let `f_a` be its original
height warp, and use the actual length and coordinate

\[
 \ell=\int_{-1}^1a(v)\,dv>0,\qquad
 X(v)=\ell^{-1}\int_{-1}^v a(s)\,ds.
\]
The accepted coordinate theorem gives `X(-1)=0`, `X(1)=1`, strict monotonicity
on the physical interval and `X'=a/ℓ>0` there. Its new smoothness theorem and the
native smooth interval inverse produce an auxiliary globally smooth extension
of the physical inverse. The native smooth quotient extension then produces a
globally smooth `K` agreeing with the accepted continuous transported curvature
on `[0,1]`. This construction works for every original `D` without additional
compatibility hypotheses.

`D.AreaNormalization` stores only this smooth `K` and its physical agreement
with the actual transported curvature. The package does not assume an action,
probe, independent derivative or safety certificate. `D.areaNormalization`
chooses it **before any probe**. Define the common smooth inverse by

\[
 V(x)=-1+\int_0^xK(t)\,dt.
\]
Physical integral congruence proves that this primitive is the physical inverse:
`V(X(v))=v` for `v∈[-1,1]` and `X(V(x))=x` for `x∈[0,1]`. It has the correct
endpoint values, `V'=K`, and sends interiors to interiors. The globally clamped
inverse is only used through its established continuous laws and physical
agreement; it is never declared globally smooth. Both moments and all
coefficient laws are derived from the same original profile:

\[
 K(X(v))=\frac{\ell}{a(v)},\qquad
 a(V(x))K(x)=\ell,\qquad
 \int_0^1K=2,\quad\int_0^1xK=1,
\]
\[
 f_K(X(v))=\frac{f_a(v)}\ell,\qquad
 f_{1,K}(X(v))=-2v. \tag{14}
\]
These equations hold on the closed physical intervals, including both poles.

For **every** smooth original height probe `R`, define `r=R∘V`. Its smoothness,
physical values and actual derivatives follow from this same map:

\[
 r(X(v))=R(v),\qquad
 r'=K(R'\circ V),\qquad
 r''=K^2(R''\circ V)+K'(R'\circ V).
\]
Differentiating the actual curvature equation on the nondegenerate closed
interval, including endpoints by derivative uniqueness, gives

\[
 K'(X(v))=-\frac{\ell^2a'(v)}{a(v)^3},\qquad
 L_Kr(X(v))=\frac{\ell}{a(v)}L_aR(v).
\]
Substitution into **every term of the complete six-entry density**, followed
by the actual Jacobian `dx=(a/ℓ)dv`, proves

\[
 A_K(R\circ V)=J_a(R),\qquad
 Q_{g_D}(M_D(R))=2\pi A_K(R\circ V). \tag{15}
\]
No unit-probe specialization or scale guess is used. The natural original-data
consumer requires only `D`, `R` and its smoothness. Conversely, any smooth area
probe `r` pulls back by `X`, and `A_K(r)=J_a(r∘X)`. Thus the entire smooth probe
class, including all smooth probe directions, is covered using fixed geometry.
The new generic closed-interval C² equality theorem supplies actual first- and
second-derivative agreement at both endpoints. The physical curvature, inverse,
probe jets and complete action are independent of the off-interval extension
choice. No Dirichlet or Neumann restriction has been added.

The original meridional form is zero exactly when `R` vanishes everywhere in
`(-1,1)`; the same holds for the azimuthal form. The proof uses the actual
cylinder pullback and endpoint covector laws. Interior nonvanishing is preserved
by `X,V`, so

\[
 M_D(R)\ne0
 \quad\Longleftrightarrow\quad
 m(K,R\circ V)>0.
\]
The same equivalence holds after the actual representing diffeomorphism.
Nonzero values only outside the physical interval do not qualify. For a
nonzero component, the existing literal probe `r/√m` has unit mass and
`Q=2πm A_K(r/√m)`. Zero components are handled separately. The new mass theorem
also retains the **actual original metric norm**, with its full scale:

\[
 \int_{S^2}|M_D(R)|_{g_D}^{2}\,d\mu_{g_D}
       =2\pi\ell^2m(K,R\circ V). \tag{16}
\]

The represented-class theorem chooses one `D`, one diffeomorphism `F` and one
normalization `N` before quantifying over all original forms and curvature boxes.
It returns `g=F* g_D`, the actual conjugated Haar projector `P_F`, its literal
meridional/azimuthal classification, and the complete original action split

\[
 Q_g(h)=2\pi\bigl[A_K(R\circ V)+A_K(S\circ V)\bigr]
                  +Q_g(h-P_Fh),\qquad Q_g(h-P_Fh)\geq0. \tag{17}
\]
The accepted equality criterion for the same remainder is retained. Original
positive curvature bounds `[κ,Λ]` give normalized bounds `[ℓκ,ℓΛ]`, with positive
lower endpoint and exact ratio `(ℓΛ)/(ℓκ)=Λ/κ`. Thus any universal unit-mass scalar
safety theorem for the stated smooth normalized moment/box class implies the
existing `rotationalSafeCaps` predicate for all original smooth forms. The
converse scalar-safety implication uses the accepted tied smooth realizer.
These are exhaustive **reduction theorems**, not a proof of safety at a new cap,
a determining characterization of the constant, or an existence theorem for an
original or relaxed optimizer.

### Round 2 native map

`N` names below have prefix
`Geometry.RotationalProfile.PoleData.AreaNormalization`; `D` names have prefix
`Geometry.RotationalProfile.PoleData`. All prefixes are relative to
`RicciFlowSharpEstimate`.

| Result | Canonical declarations |
|---|---|
| Actual endpoint derivative agreement | `Analysis.eqOn_derivatives_Icc` in `Analysis/ClosedIntervalDerivatives.lean` |
| Smooth coordinate and original-data producer | `Geometry.ReciprocalArea.coordinate_contDiff`, `D.AreaNormalization`, `D.nonempty_areaNormalization`, `D.areaNormalization` in `Geometry/SmoothAreaNormalization.lean` |
| Common smooth inverse, moments and coefficients (14) | `N.inverse_contDiff`, `inverse_hasDerivAt`, `inverse_coordinate`, `coordinate_inverse`, `curvature_pos`, `integral_curvature`, `integral_mul_curvature`, `curvature_coordinate`, `warp_coordinate`, `warpSlope_coordinate` in the same module |
| Original physical nonzero criteria | `D.meridionalOneForm_eq_zero_iff`, `meridionalOneForm_ne_zero_iff`, their azimuthal siblings in `Geometry/PhysicalProbeNonzero.lean` |
| Actual probe jets and full density/action (15) | `N.deriv_probe`, `deriv_deriv_probe`, `curvature_deriv_coordinate`, `meridionalOperator_coordinate`, `meridionalDensity_coordinate`, `meridionalAction_eq`, `oneFormDissipation_meridional_eq` in `Geometry/NormalizedAreaAction.lean` |
| Off-interval independence and reverse probe coverage | `N.curvature_deriv_eq_on`, `probe_derivatives_eq_on`, `meridionalAction_extension_independent`, `probe_comp_coordinate`, `meridionalAction_comp_coordinate`; `Geometry.AreaProfile.meridionalAction_congr` in the same module |
| Physical mass, literal normalization and actual norm (16) | `N.probe_nonzero_iff`, `probeMass_pos_iff_meridional_ne_zero`, its azimuthal sibling, `normalized_probe_action`, `integral_normSq_eq_probeMass` in `Geometry/NormalizedAreaMass.lean` |
| Scaled curvature and represented nonzero/action | `N.curvature_inverse`, `profile_mul_curvature`, `curvature_bounds_scaled`, the two `probeMass_pos_iff_pullback_*_ne_zero` theorems and `oneFormDissipation_pullback_meridional_eq` in `Geometry/NormalizedAreaHaar.lean` |
| Fixed-representation full Haar split (17) | `N.exists_conjugated_haar_area_dissipation`, `Geometry.IsRepresentedRotationalMetric.exists_normalized_area_representation` in the same module |
| Natural original-data and safety consumers | `D.oneFormDissipation_eq_normalizedAreaAction`, `N.oneFormDissipation_nonneg_of_normalized_safety`, `Geometry.rotationalSafeCaps_of_normalized_area_safety`, `Geometry.areaAction_nonneg_of_rotationalSafeCap` in the same module |

The six new canonical leaves contain 58 public theorems, three definitions and
one extension structure. Their evidence is recorded in the
[Round 2 native receipt](../evidence/phase2-round-2/receipt.json) and
[checkpoint record](../evidence/phase2-round-2/checkpoint.json). The single Round 2 outer review passed at `734dd5b`, including both delivered
checkpoints. The unchanged Round 0 and Round 1 reviews remain accepted. Phase-I source, paper and evidence bytes remain preserved.

Additional native regression checks use `D.a=c` for **arbitrary `c>0`**:
`ℓ=2c`, `X(v)=(v+1)/2`, physical `K=2` and `V(x)=2x−1`.
Both sides of (15) give `4/3` for `R=1` and `20/3` for the nonconstant `R(v)=v`;
the corresponding original geometric dissipations are `8π/3` and `40π/3`.
A separate consumer uses arbitrary `D,R` with no supplied coordinate equations.
These are exact kernel checks, not numerical evidence for a sharp value.

### Round 2 continuation: actual original-form variations

The same smooth normalization transports actual original-form variations at
arbitrary original scale. Two further native modules give direct geometric
consumers of the complete action and quotient calculus.
Fix the original `D` and its normalization **before** smooth probes `R,S`, and
write `r=R∘V`, `s=S∘V`. The actual original-form variation satisfies

\[
 \frac{d}{dt}\bigg|_0 Q_{g_D}(M_D(R+tS))
       =4\pi\int_0^1f_KsE_Kr. \tag{18}
\]
The same formula holds after the actual representing diffeomorphism, with the
same pullback metric, varying pullback form and fixed normalization. No profile
compatibility premise or new geometry is requested of the caller.

Stationarity of this original dissipation along **every original smooth
meridional direction** is equivalent to `E_Kr=0` on `[0,1]`. For the exhaustive
implication, any smooth area direction `s` comes from the actual original
`S=s∘X`; physical equality suffices inside the integral. The reverse implication
uses the same complete pairing. No endpoint restriction, nonzero kernel or
full joint optimizing pair is asserted.

Let the physical quotient use the literal original norm and volume:

\[
 \mathcal Q_D(R)=
 \frac{Q_{g_D}(M_D(R))}{\int_{S^2}|M_D(R)|_{g_D}^2\,d\mu_{g_D}}.
\]
The exact mass factor in (16) gives

\[
 \mathcal Q_D(R)=\ell^{-2}\mathcal R(K,r),\qquad
 \frac{d}{dt}\bigg|_0\mathcal Q_D(R+tS)
 =\frac{2}{\ell^2m(K,r)}\int_0^1 f_Ks
       [E_Kr-\mathcal R(K,r)r]. \tag{19}
\]
The derivative assumes the actual original form is nonzero, which supplies
positive physical mass. The algebraic quotient identity also handles zero mass
using Lean's totalized real division; no unit normalization or spectral meaning
is assigned to the zero form.

A local minimum of the **literal original quotient** along every original smooth
meridional direction therefore implies
`E_Kr=𝓡(K,r)r` on the closed physical interval. Its proof transports all directions
and reuses the accepted scalar stationarity equivalence. The coefficient is the
actual scalar quotient, or `ℓ²𝒬_D(R)`; it is not silently replaced by zero. This
is a fixed-geometry necessary-condition application. It still supplies no joint
minimum, critical-object existence or moment multiplier. Since ℓ varies with the
metric, the physical quotient itself is not invariant under metric scaling.
A future joint-minimum application must retain the normalized geometry scale
or the equivalent ℓ² correction; a minimum over unnormalized physical quotients
cannot simply be substituted for the normalized scalar problem.

| Result | Declaration, in `Geometry.RotationalProfile.PoleData.AreaNormalization` |
|---|---|
| Actual original dissipation derivative (18) | `oneFormDissipation_meridional_hasDerivAt` in `Geometry/NormalizedAreaVariation.lean` |
| Exhaustive original-direction stationarity | `oneFormDissipation_meridional_stationary_iff` in the same module |
| Same represented metric/form variation | `oneFormDissipation_pullback_meridional_hasDerivAt` in the same module |
| Literal physical quotient and derivative (19) | `oneFormDissipation_div_normSq_eq`, `oneFormDissipation_div_normSq_hasDerivAt` in `Geometry/NormalizedAreaRayleigh.lean` |
| Necessary condition from original directional minima | `oneFormDissipation_div_normSq_euler_eq_of_isLocalMin` in the same module |

The [continuation native receipt](../evidence/phase2-round-2-continuation/receipt.json)
reuses the unchanged initial Round 2 native inputs and records fresh checks of
these two leaves and the affected root. The single outer review of the coherent Round 2 packet passed at `734dd5b`;
unchanged mathematics and its matching native evidence remain accepted.

## Round 3: complete-action coercivity and both-pole mass control

Let `K` be continuous and `r` be C² on the real line. Assume the actual normalized
moments and a positive physical curvature box `0<κ≤K≤Λ` on `[0,1]`. These hypotheses
include every original smooth normalized competitor. No derivative of K is
bounded or used in the following estimate. Write

\[
 m=\int_0^1fr^2,\qquad U=\int_0^1r^2,\qquad
 \mathcal E=\int_0^1 f(L_Kr)^2,\qquad
 \mathcal G=\int_0^1 f^2(r')^2.
\]
Here `f=warp K`, its slope is the actual primitive `b=warpSlope K`, and `L_K`
uses the actual first and second derivatives of r. The energy `𝓔` is distinct
from the fourth-order Jacobi operator `E_K` used in earlier sections.

The native comparison of second derivatives and the two pole values gives

\[
 \kappa x(1-x)\leq f(x)\leq\Lambda x(1-x),\qquad
 |b(x)|\leq2,\qquad 0\leq f(x)\leq2\min(x,1-x). \tag{20}
\]
The quadratic comparisons require only the corresponding curvature bound and
moments. Nonnegative curvature suffices for the slope and two-pole upper bound.
No symmetry of the geometry or probe is assumed.

The actual weighted operator flux satisfies

\[
 (f^2r'r)'=frL_Kr+f^2(r')^2+fKr^2.
\]
The moments imply `f(0)=f(1)=0`, so both flux values vanish for every C² probe,
with unrestricted probe endpoint values. Integrating gives

\[
 \int_0^1frL_Kr=-\mathcal G-\int_0^1fKr^2.
\]
Multiplying a square by the nonnegative warp and integrating then proves the
parameterized interpolation estimate

\[
 4t\mathcal G\leq4t^2\mathcal E+m\qquad(t\geq0). \tag{21}
\]
This calculation retains the curvature term with its actual nonnegative sign.

For `w=x(1-x)`, a separate generic C¹ Hardy estimate is

\[
 U\leq12\int_0^1wr^2+4\int_0^1w^2(r')^2.
\]
It comes from the exact derivative of `w(1−2x)r²`, whose two boundary values are
zero, and a scalar square inequality. The numbers are consequences of that flux
and the absorption, not proposed values of a threshold. Transferring this estimate
through (20) gives

\[
 \kappa^2U\leq12\kappa m+4\mathcal G. \tag{22}
\]

The proof estimates the **original complete density**, not its smooth K′
factorization. For `q=L_Kr`, the explicit nonnegative-square decomposition implies

\[
 f q^2-Kbr(fp+br/2)+K^2fr^2
       \geq f q^2-\Lambda f^2p^2-3\Lambda r^2,
 \qquad p=r'.
\]
Thus `A≥𝓔−Λ𝓖−3ΛU`. Set

\[
 d=\Lambda(1+12/\kappa^2),\qquad
 \Gamma(\kappa,\Lambda)=\frac{d^2}{2}
             +\frac{36\Lambda}{\kappa}+\frac3\kappa+\frac1{\kappa^4}\geq0.
\]
Using (21) at `t=1/(2d)` and `t=κ²/4`, together with (22), yields respectively

\[
 \frac{\mathcal E}{2}\leq
 A+\left(\frac{d^2}{2}+\frac{36\Lambda}{\kappa}\right)m,
 \qquad
 U\leq\mathcal E+\left(\frac{12}{\kappa}+\frac4{\kappa^4}\right)m.
\]
The resulting homogeneous complete-action coercivity theorem is

\[
 \boxed{\ \frac{\mathcal E+U}{4}\leq A_K(r)+\Gamma(\kappa,\Lambda)m(K,r)\ }. \tag{23}
\]
The constants are chosen before K and r, depend only on the positive box, and
require no bounds on curvature derivatives. Negative action is allowed; the mass
correction in (23) is essential. This estimate supplies no new safe cap.

For `m=1` and `A≤B`, both `𝓔` and U are at most `4(B+Γ)`. The actual sum of the
weighted masses near the two poles is

\[
 P_\delta(K,r)=\int_0^\delta fr^2+\int_{1-\delta}^1fr^2.
\]
For every `0≤δ≤1`, (20) and integral monotonicity prove

\[
 0\leq P_\delta(K,r)\leq4\delta U
                  \leq16\delta(B+\Gamma). \tag{24}
\]
The two intervals may overlap; both contributions remain in the definition.
For every ε>0, the explicit choice

\[
 \delta_\varepsilon=
 \min\!\left(1,\frac{\varepsilon}{16(\max(B,0)+\Gamma)+1}\right)>0
\]
works for every admissible K,r and every radius `0≤t≤δ_ε`. This proves a single
modulus tending to zero for both weighted polar masses, uniformly over any
varying sequence with these bounds. No geometry or probe is chosen before the
uniform radius in that theorem.

The original ratio restriction is retained in the cap-class consumers. From
`∫K=2`, a positive box `[κ,Λ]` and `Λ/κ≤C`, integration of the box gives
`κ≤2≤Λ`, hence `2/C≤K≤2C`. The latter is an auxiliary common box for the estimate;
it does not replace the original ratio restriction. The native ratio-class
coercivity and polar-radius statements keep κ, Λ, their positive lower bound,
and `Λ/κ≤C` explicitly in their hypotheses. Their constants depend only on C
(and the action bound for the radius), even when the original boxes vary.

### Round 3 native map and scope

Geometry names in the table have prefix `Geometry.AreaProfile`; all prefixes are
relative to `RicciFlowSharpEstimate`.

| Result | Canonical declaration or source |
|---|---|
| Actual warp, slope and ratio bounds (20) | Six theorems in `Geometry/AreaWarpBounds.lean`, including `warp_bounds_of_curvature_bounds`, `warp_nonneg_le_two_mul_min`, `curvature_bounds_of_ratio` |
| Generic C¹ Hardy estimate | `Analysis.integral_sq_le_parabolic_weighted_energy` in `Analysis/ParabolicWeightedHardy.lean` |
| Actual energies and C² operator continuity | `probeOperatorEnergy`, `probeGradientEnergy`, `meridionalOperator_continuous_of_contDiff_two` in `Geometry/AreaProbeEnergy.lean` |
| Actual flux pairing and interpolation (21) | `integral_warp_mul_probe_operator`, `probeGradientEnergy_interpolation` in the same module |
| Transfer of Hardy (22) | `integral_sq_le_probeMass_gradient` in the same module |
| Complete density bound and homogeneous coercivity (23) | `probeOperatorEnergy_sub_le_action`, `actionMassCorrection`, `meridionalAction_coercive`, `exists_uniform_action_coercivity` in `Geometry/AreaActionCoercivity.lean` |
| Actual two-tail mass | `polarProbeMass`, `polarProbeMass_nonneg`, `polarProbeMass_le_four_mul_radius` in `Geometry/AreaPolarMass.lean` |
| Unit-mass bounds and uniform radius (24) | `probe_energies_le_of_unit_mass_action_le`, `polarProbeMass_le_of_unit_mass_action_le`, `exists_uniform_polar_mass_radius` in `Geometry/AreaActionCoercivity.lean` |
| Original ratio-class consumers | `meridionalAction_coercive_of_curvature_ratio`, `exists_uniform_polar_mass_radius_of_ratio` in the same module |

The packet has five new canonical leaves, 24 public theorems and four definitions.
Its [native receipt](../evidence/phase2-round-3/receipt.json) and
[checkpoint record](../evidence/phase2-round-3/checkpoint.json) bind the final inputs
and validation. The configured single Round 3 outer review is pending. Accepted
Phase-I and Phase-II rounds 0–2 remain preserved. The first-phase TeX/PDF is unchanged.

Exploratory exact rational polynomial integration tested `K=2` with `(1−x)^n`
and `x^n`, concentrating near the two different poles, before the coercivity
consumers were promoted. These computations were stress tests, not theorem
evidence. Additional native consumer checks cover both polynomial families for
**every natural n**, and a varying sequence of curvatures, probes and original
ratio boxes with unit mass, a common action bound and one shared radius. The actual proof of (23) is uniform over all
stated competitors and does not rely on those examples.

## Round 3 continuation: direct control of the remaining polar terms

The initial Round 3 estimate controls weighted mass. The continuation proves
additional derivative estimates and **direct** unweighted/remainder tail bounds;
these are not inferred from weighted mass tightness alone. Keep the actual
primitives f,b, operator q=L_Kr and positive box κ≤K≤Λ with both exact moments.
Continuous K and C² r still suffice, with no curvature derivative bound.
Put w(x)=x(1−x) and

\[
 H=\int_0^1 w(r')^2,\qquad J=\int_0^1 f^3(r'')^2.
\]

The actual flux `2 f² b (r′)²` vanishes at both poles. Its derivative, using
`f′=b` and `b′=−2K`, gives

\[
 \int_0^1 f(q+Kr)^2=J+4\int_0^1 f^2K(r')^2,
 \qquad J\leq2E+2\Lambda^2m. \tag{25}
\]

This identity does not differentiate K or require pole values of r or r′ to
vanish. A separate polynomial flux `w²(1−2x)p²` gives, for every C¹ function p,

\[
 \int_0^1 wp^2\leq10\int_0^1w^2p^2+\int_0^1w^3(p')^2.
\]

Apply it to p=r′, use f≥κw, (25), and (21) at t=1 to obtain

\[
 \kappa^3H\leq(10\kappa+2)E+
       (5\kappa/2+2\Lambda^2)m. \tag{26}
\]

For m=1 and A≤B, let D=max(B,0)+Γ(κ,Λ). One explicit bound chosen before all
competitors is

\[
 M=1+4D+
   \frac{4(10\kappa+2)D+5\kappa/2+2\Lambda^2}{\kappa^3}>0.
\]

Then E,U,G,H≤M. The first-power weight in H is stronger at the poles than the
squared-warp gradient bound G used in the initial coercivity argument.

For C¹ r define its two unweighted tails
`T_s=∫₀ˢr²+∫₁₋ₛ¹r²`. A tent with branches `(1−s)x` and `s(1−x)` has squared
height at most `s w`. Integrate the derivative of each affine branch times r²;
the internal boundary terms cancel exactly. The square inequality and reflection
then yield, for 0≤s≤1, a>0 and s≤a²,

\[
 T_s\leq2sU+2a(U+H). \tag{27}
\]

The second term is essential: a bound on U alone would not give uniform tail
integrability. The proof has no singular division by the vanishing warp and no
artificial endpoint condition.

The canonical remainder is defined by literal subtraction from the original
six-entry density:

\[
 R_K(r)=\operatorname{density}_K(r)-f(L_Kr)^2
       =-Kbfrr'-Kb^2r^2/2+K^2fr^2.
\]

Let `S_s=∫₀ˢ|R_K(r)|+∫₁₋ₛ¹|R_K(r)|`, the actual `polarActionRemainder`.
The already proved bounds |b|≤2 and 0≤f≤1, followed by a parameterized square
estimate, give for every t>0

\[
 S_s\leq(\Lambda/t+2\Lambda+\Lambda^2)T_s+2\Lambda tG. \tag{28}
\]

This controls the absolute complete remainder, including its negative unweighted
term and mixed derivative term. It does not replace either with a K′ potential.
For 0<t≤1 and 0≤s≤t⁴, apply (27) with a=t² and the common M bound:

\[
 T_s\leq6t^2M,\qquad
 S_s\leq(20\Lambda+6\Lambda^2)tM.
\]

Set Q=(6+20Λ+6Λ²)M, t=min(1,ε/(Q+1)), and δ=t⁴. For every ε>0 this δ>0,
δ≤1 works for **every** admissible K,r and **every** width 0≤s≤δ, with
`T_s≤ε` and `S_s≤ε`. The same theorem has an original-ratio consumer: C≥1,
varying κ,Λ>0 and Λ/κ≤C remain explicit, while the auxiliary [2/C,2C] box permits
one common radius before all competitors. No optimizer symmetry is assumed.

The continuation adds these native targets:

| Result | Canonical declarations (relative prefixes as above) |
|---|---|
| Weighted interpolation | `Analysis.integral_parabolic_mul_sq_le` in `Analysis/ParabolicDerivativeEnergy.lean` |
| Direct one- and two-pole unweighted estimates | `Analysis.integral_left_sq_le_parabolic_energy`, `Analysis.integral_polar_sq_le_parabolic_energy` in `Analysis/ParabolicPolarControl.lean` |
| Actual second-derivative identity and both derivative bounds | `integral_warp_operator_add_curvature_sq`, `integral_warp_cube_second_deriv_sq_le`, `integral_parabolic_deriv_sq_le` in `Geometry/AreaProbeRegularity.lean` |
| Complete remainder, absolute tails and (28) | `meridionalActionRemainder`, its C¹ continuity theorem, `polarActionRemainder`, `polarActionRemainder_le` in `Geometry/AreaActionPolarControl.lean` |
| Uniform sublevel and original-ratio consumers | `exists_uniform_probe_regularity_bound`, `exists_uniform_polar_action_radius`, `exists_uniform_polar_action_radius_of_ratio` in the same module |

These are four additional canonical leaves, eleven public theorems and two
definitions. Their final native receipt is recorded under
`docs/evidence/phase2-round-3-continuation/`. The single configured Round 3 outer
review remains pending for the combined packet; no independent acceptance is
inferred from the source simplifier advisory.

## Round 4 initial checkpoint: actual weak domain and a joint unit-mass limit

Round 3's combined estimate packet passed its single outer review at `2778716`.
Round 4 consumes those estimates to construct a limit; it does not supply
compactness or a limiting pair as a theorem premise. The native statement is
`Geometry.AreaProfile.exists_normalized_joint_weak_limit` in
`Geometry/AreaJointCompactness.lean`.

### The domain and its actual derivatives

Write U=(0,1), μ=Lebesgue measure restricted to U, and w(x)=x(1−x).
`Analysis.HasWeakDerivOn U r p` requires local integrability of both representatives
and the genuine distributional identity

\[
 \int_{\mathbb R}\varphi' r=-\int_{\mathbb R}\varphi p
 \quad\text{for every }\varphi\in C_c^\infty(U). \tag{29}
\]

The test products are proved integrable. The fundamental lemma for smooth
compact tests proves a.e. uniqueness of p; changing representatives a.e. preserves
the relation. `HasParabolicWeakDerivatives r p z` requires this relation for r,p
and for p,z, together with

\[
 r\in L^2(\mu),\qquad \sqrt w\,p\in L^2(\mu),\qquad
 w\sqrt w\,z\in L^2(\mu). \tag{30}
\]

Both derivatives belong to ordinary L² on every compact subset of U, because
the reciprocal weights are bounded there. Thus the domain has the stated local
second-order Sobolev regularity, expressed with genuine weak derivatives and L²
membership. Every globally C² probe embeds with its actual first and second
derivatives. No endpoint value or derivative trace is prescribed. Zero extensions
used to select representatives outside U are not trace conditions on this domain.
The final predicates use conjunctions with named theorem projections; their
conditions are not compiler-generated proof definitions.

### The constructed subsequence

Consider arbitrary sequences of continuous curvatures K_n and C² probes r_n,
positive box witnesses κ_n,Λ_n with Λ_n/κ_n≤C, C≥1, both exact normalized moments,
unit actual mass, and a common complete-action bound A(K_n,r_n)≤B. Then there
exist one strictly increasing φ:ℕ→ℕ, K_0,r_0,p_0,z_0 and κ_0,Λ_0 with:

- K_0 in L² and L∞ on U; κ_0>0, κ_0≤K_0≤Λ_0 a.e., Λ_0/κ_0≤C, and both
  original moments exactly 2 and 1. The original scalar witnesses κ_n,Λ_n
  converge to κ_0,Λ_0 on this same subsequence.
- Weak-* curvature convergence in the literal form of convergence of
  `∫K_(φ(n)) v` to `∫K_0 v` for **every** integrable real test v on U.
- Uniform convergence of the original `warp K_(φ(n))` and `warpSlope K_(φ(n))`
  on [0,1] to the original primitives of K_0. These limits are continuous on
  [0,1], retain both pole values, both slope values, the quadratic comparison
  with [2/C,2C], and the absolute slope bound 2. They satisfy the actual weak
  derivative laws Df=b and Db=−2K_0.
- `HasParabolicWeakDerivatives r_0 p_0 z_0`; r_0,p_0 are continuous on U.
  The probes converge strongly in L²(μ), and the probes and their actual first
  derivatives converge locally uniformly on U. The weighted actual second
  derivatives converge weakly in L² to w√w z_0, with every L² test retained.
- Genuine integrability and exact retention of the original mass

\[
 \int_0^1 f_{K_0}r_0^2=1,\qquad
 \exists x\in(0,1),\quad r_0(x)\ne0. \tag{31}
\]

  The result also supplies integrability of the literal complete weak density
  and L² membership of both its positive-square factors described below.

All these are conclusions of the producer. No limit, weak derivative, local
compactness property, preserved normalization or original-ratio retention is
assumed. The auxiliary common box [2/C,2C] controls constants; the returned
κ_0,Λ_0 retain the actual original ratio restriction separately.

Here is the dependency route used in the proof. The accepted coercivity and
parabolic estimates uniformly bound U,H and the weighted second derivative
energy. On every interior interval, the weight has a positive lower bound.
The actual FTC and an integrated square give

\[
 (r(x)-r(y))^2\leq |x-y|\int_a^b(r')^2,
 \quad (b-a)r(x)^2\leq2\int_a^b r^2+2(b-a)^2\int_a^b(r')^2. \tag{32}
\]

These give pointwise boundedness and equicontinuity for the probes and their
first derivatives on interior intervals. Sequential Arzela–Ascoli in the
compact-open topology produces locally uniform limits on all of U. The
verified unweighted polar estimate makes this family uniformly L² integrable;
Vitali convergence then upgrades the probe limit to global strong L².

The weighted second derivatives are extracted by sequential Banach–Alaoglu
and the native Riesz isometry for the real Hilbert space L²(μ). If their weak
limit is Z, set z_0=Z/(w√w) on U. A compact test divided by this nonvanishing
interior weight is itself an L² test. Passing the actual integration-by-parts
identity to the limit identifies Dp_0=z_0. Fatou's bound supplies the weighted
L² membership of p_0. This constructs the weak graph rather than assuming it.

For curvature, the original mean and ratio give
`κ_n∈[2/C,2]` and `Λ_n∈[2,2C]`. Compactness first extracts both scalars together;
Hilbert weak compactness then extracts the actual curvature. Testing a weak
limit against its negative part proves a.e. order closure, including varying
scalar bounds. The tests 1 and x preserve both moments. A common essential
bound extends L² pairings to all L¹ tests by bounded continuous approximation.
The indicator tests `1_(0,x)` and `(x−s)1_(0,x)` identify the original primitives,
including both endpoints; their common Lipschitz bounds upgrade this convergence
to uniform convergence. Later subsequences preserve every earlier convergence.

Finally, uniform warp convergence yields strong L∞ convergence of its coefficient,
while probes converge strongly in L². The native continuous L∞×L²→L² multiplier
and the L² inner product prove weighted square-integral convergence, hence (31).
This uses the uniformly converging **warp**, not a fictitious strong curvature
limit. A separate native argument also retains `∫r_0²≥1` from unit mass and f_n≤1,
which certifies physical nontriviality before the final weighted-mass assembly.

### Literal weak action, and what has not been proved

The geometric weak operator and action use the original primitives and the tied
weak derivatives from (29)–(30):

\[
 q=fz+2bp-Kr,\qquad
 A=\int_0^1\operatorname{meridionalActionDensity}(f,b,K,r,p,z). \tag{33}
\]

Under the actual coefficient bounds produced above, the graph gives
`√f q∈L²` and `√f(Kr)∈L²`. It also makes the mixed and negative terms integrable.
The native decomposition is exactly

\[
 A=\int f\,[q^2+(Kr)^2]-\int Kbfrp-\tfrac12\int Kb^2r^2. \tag{34}
\]

Specializing p,z to actual smooth derivatives agrees with `meridionalAction`
by definition. No totalized classical derivative is used for the weak limit,
and no K′ potential or missing jump/interface contribution replaces the density.
The coefficient-bound action lemma is an explicit auxiliary estimate; the joint
producer discharges all its premises for the returned object.

At the initial `0fe2595` checkpoint, full-action lower semicontinuity and the
two positive-square weak identifications were still open. The continuation below
supplies those identifications and the linear-K pairing limits. It does not
replace them with convergence of the whole remainder.

The review's oscillating example `K_n=2+cos(2πnx)` was checked as an exploratory
diagnostic using its actual primitives and normalized constant probe. Numerical
quadrature for n=1,4,16,64 keeps the curvature-square integral near 4.5 while
its complete actions tend toward 5 and its integrated remainders toward 0.5;
the limiting constant pair has action 4 and remainder 0. These computations
are **not** native theorem evidence. They confirm the need to retain both
positive squares in (34), and are not an asserted counterexample to lower
semicontinuity. No new sharp-cap value is inferred.

### Round 4 native map

All prefixes below are relative to `RicciFlowSharpEstimate`.

| Mathematical layer | Canonical sources and principal consumers |
|---|---|
| Weak derivative and weighted domain | `Analysis/WeakDerivative.lean`, `Analysis/ParabolicSobolev.lean`: `HasWeakDerivOn`, `HasParabolicWeakDerivatives`, a.e. uniqueness, smooth embedding and local L² |
| Actual interior compactness | `Analysis/IntervalDerivativeEnergy.lean`, `Analysis/LocallyUniformSubsequence.lean`, `Analysis/InteriorSobolevCompactness.lean`: actual interval bounds and `exists_subseq_locallyUniform_probe_deriv_of_weighted_energy` |
| Native weak Hilbert and curvature order limits | `Analysis/HilbertWeakSubsequence.lean`, `Analysis/L2WeakOrder.lean`, `Analysis/BoundedWeakPairing.lean` |
| Global probe convergence and identified weak derivatives | `Analysis/L2UniformIntegrability.lean`, `Analysis/WeakDerivativeLimits.lean`, `Analysis/WeightedWeakDerivativeLimit.lean` |
| Weighted mass continuity | `Analysis/L2WeightedMassContinuity.lean` |
| Actual curvature/scalar extraction | `Geometry/AreaCurvatureCompactness.lean`: `exists_curvature_subsequence_of_ratio_bound` |
| Original primitive identification and weak geometry | `Geometry/AreaWeakPrimitives.lean`, `Geometry/AreaUniformPrimitives.lean` |
| Actual sublevel probe producer | `Geometry/AreaProbeCompactness.lean`: `exists_subseq_strong_probe_of_action_bound`, `exists_subseq_weak_probe_of_action_bound` |
| Genuine weak action domain | `Geometry/WeakAreaAction.lean`: `weakMeridionalOperator`, `weakMeridionalAction`, positive-square membership, full density integrability and (34) |
| Joint unit-mass producer | `Geometry/AreaJointCompactness.lean`: `exists_normalized_joint_weak_limit` |

The 18 new leaves have final native evidence recorded separately in
`docs/evidence/phase2-round-4/`. Their single configured outer review remains
pending. Accepted rounds 0–3, Phase I, its paper bytes and all earlier receipts
remain unchanged.

## Round 4 continuation: the complete-action liminf of the original sequence

The continuation consumes the actual joint limit above. Its main theorem is
`Geometry.AreaProfile.exists_normalized_joint_weak_limit_le_liminf_action` in
`Geometry/AreaJointActionCompactness.lean`. Under the same smooth sublevel inputs,
it retains every conclusion of the initial joint producer and adds weak L²
pairings for both `√f_n q_n` and `√f_n K_n r_n`, together with

\[
 A_{\mathrm{weak}}(K_0,r_0,p_0,z_0)
 \leq \liminf_{n\to\infty} A(K_n,r_n). \tag{35}
\]

The right side is the liminf of the **original sequence**. It is not merely the
liminf along an arbitrary extracted subsequence. The complete density, its mixed
term, negative potential and positive curvature square are all retained.

### Identifying both positive factors

Write the actual graph coordinates as

\[
 P_n=\sqrt w\,r_n',\qquad Z_n=w\sqrt w\,r_n''.
\]

`exists_uniform_parabolic_graph_bound` derives a common L² bound for r_n,P_n,Z_n
from the accepted complete-action and derivative estimates. The initial producer
already gives weak convergence of Z_n and pointwise interior convergence of P_n.
On the finite physical measure space, the latter and its uniform L² bound imply
weak L² convergence against every L² test.

For the derivative part of the operator, use the actual coefficients

\[
 a_n=\frac{f_n\sqrt{f_n}}{w\sqrt w},\qquad
 c_n=\frac{2b_n\sqrt{f_n}}{\sqrt w}.
\]

They are evaluated a.e. in (0,1), where the denominators are nonzero. The actual
warp/slope estimates imply

\[
 0\leq a_n\leq\Lambda\sqrt\Lambda,\qquad
 |c_n|\leq4\sqrt\Lambda,
 \quad
 \sqrt{f_n}(f_n r_n''+2b_n r_n')=a_nZ_n+c_nP_n. \tag{36}
\]

Pointwise primitive convergence gives pointwise convergence of these bounded
coefficients. A native dominated-convergence lemma makes each coefficient times
one fixed L² test converge strongly in L². Weak/strong pairing then identifies
the weak limit in (36). This does not require uniform relative warp convergence
at the poles, a curvature derivative, or energy-tail vanishing.

For the curvature factor, testing `√f_n K_n r_n` against v in L² amounts to
pairing K_n with `r_n√f_n v`. The following native product principle supplies
strong L¹ convergence of that varying test:

\[
 x_n\longrightarrow x\text{ strongly in }L^2,\quad
 y_n\longrightarrow y\text{ a.e.},\quad
 \sup_n\|y_n\|_2<\infty
 \quad\Longrightarrow\quad
 \int|x_ny_n-xy|\longrightarrow0. \tag{37}
\]

Here the measure is finite and membership of the limit y in L² is derived by
Fatou. The proof establishes native uniform integrability using restricted
Hölder estimates and applies Vitali convergence; uniform integrability is not
an extra conclusion-containing premise. Apply (37) with x_n=r_n and
`y_n=√f_n v`. Bounded weak curvature pairings against all L¹ tests then give the
claimed potential-factor weak limit. Subtracting this from (36) identifies the
actual full factor `√f_n q_n`. Both factors and their limits have genuine L²
membership.

### Passing the signed terms and the complete action

The same product principle handles the coefficient of K in each signed term.
For the mixed term take `y_n=b_n f_n r_n'`; for the negative potential take
`y_n=b_n²r_n`. The pointwise limits come from the actual primitive and local
probe/derivative convergence. Their global L² bounds follow from

\[
 |b_nf_nr_n'|\leq2\Lambda|\sqrt w\,r_n'|,
 \qquad |b_n^2r_n|\leq4|r_n|. \tag{38}
\]

Consequently `b_n f_n r_n r_n'` and `b_n²r_n²` converge strongly in L¹ on the
whole physical interval. Pairing these with the uniformly bounded weak curvature
proves convergence of both literal signed integrals. Their limiting products
are proved integrable. The previously verified polar estimates enter through
global strong L² probe convergence; no additional tail assumption is introduced.

For each positive square, the supporting inequality

\[
 \int u_n^2\geq2\int u_nu_0-\int u_0^2
\]

and the identified weak pairing give lower semicontinuity. Adding both inequalities
and subtracting the genuinely converging signed integrals gives the full action
inequality. Concentration of positive operator energy is allowed. In particular,
no convergence of the whole remainder or action under oscillating curvature is
asserted; the diagnostic preceding this continuation remains relevant.

Finally, the mass-corrected coercivity bounds the smooth actions below by a finite
box-dependent constant, while the input sublevel bounds them above. A genuine
strictly increasing liminf subsequence is selected first. The initial joint
compactness producer then selects a further subsequence; all of its constraints,
weak derivatives, masses and convergences remain on the composed subsequence.
The new full-action inequality and scalar action convergence yield (35) for the
original sequence. No supplied weak pair, action minimum, compactness conclusion
or lower-semicontinuity conclusion is an input of this strengthened producer.

### Continuation native map and scope

| Role | Canonical source |
|---|---|
| Uniform integrability and strong L¹ products | `Analysis/L2PointwiseProducts.lean` |
| Weak/strong L² pairings and bounded varying multipliers | `Analysis/L2WeakMultipliers.lean` |
| Bounded curvature with varying strong L¹ tests | `Analysis/BoundedWeakPairingLimits.lean` |
| Weak square-integral lower semicontinuity | `Analysis/L2WeakLowerSemicontinuity.lean` |
| Actual uniform graph-coordinate bounds | `Geometry/AreaSublevelGraphBounds.lean` |
| Identified derivative-part weak limit | `Geometry/AreaDerivativeProductLimit.lean` |
| Curvature factor and both signed integral limits | `Geometry/AreaCurvatureProductLimits.lean` |
| Both full weak factors and complete-action LSC in the area topology | `Geometry/AreaActionLowerSemicontinuity.lean` |
| Actual constrained joint limit satisfying (35) | `Geometry/AreaJointActionCompactness.lean` |

The nine leaves add 18 public theorems. Native continuation evidence is recorded
in `docs/evidence/phase2-round-4-continuation/`; the initial `0fe2595` source and
receipt remain unchanged. One configured outer review remains pending for the
combined Round 4 packet. This closes the native limiting-action checkpoint;
it does not establish unrestricted smooth recovery or identify C_rot.

## Exact frontier and next target

Phase I remains COMPLETE and Phase II remains OPEN. The accepted Round 3 estimates
are preserved. Round 4 now constructs a joint normalized weak limit retaining the
original ratio/moments and unit physical mass, identifies both positive-square
weak factors, and proves full-action lower semicontinuity with comparison to the
liminf of the original sequence. Its one configured outer review remains pending.
No optimizer, determining value, selected threshold branch, new universally safe
cap or unrestricted endpoint statement is claimed.

T7 remains active for unrestricted derivative-sensitive smooth recovery. The next
executable target is probe density in the actual weighted graph norm, including
endpoint approximation without imposing a permanent pole condition, followed by
nonsymmetric measurable-curvature recovery with exact moments, positivity and the
original ratio. Control relative warp errors at both poles when passing the
second-derivative square. Every term of the complete action and the physical mass
must converge; then apply literal positive normalization and the tied original
metric/form realizer. The older symmetric monotone fixed-probe recovery is not a
substitute. No required bridge is deferred out of the original goal.

T5 still requires a produced joint minimizing/critical object and justified feasible
variations, with the scale-correct normalized objective. No moment multipliers,
symmetry, fixed switch count, probe sign, smooth attainment or zero eigenvalue is
inferred. T8–T10 still require a genuinely determining characterization and justified
selection, universal complete-action safety, original smooth negative witnesses
below every larger cap, and the precise unrestricted endpoint scope. Final T11
still depends on these mathematical, native, independent-review and delivery gates.
