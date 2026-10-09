# Mathematical scope and dependency graph

This project is incomplete. Native layers prove the all-cap parameter, the generic
exact deficit, the actual continuous admissible obstacle candidate, its contacts
and actual prefix/tail primitives, its explicit marginal calibration and minimization,
the exact all-cap value, interval uniqueness, both contact derivative jumps and
strictness for differentiable competitors, and a quantitative exponential tangent
estimate. The actual weighted variance identity and obstacle anchor now prove
L² stability with constant `[12C/(5α) + log C/(2α³)]⁻¹`, including cap one,
and the two hemisphere deficits control reflection and symmetrization errors.
The native smooth metric producer now retains the original balanced profile,
globally removable pole factors and actual sphere tensor law, with a scaled-round
constant-profile witness. The actual cylinder pullback, global volume density and
height disintegration are now native. The intrinsic scalar/sectional curvature
formulas also hold on the entire sphere, including the poles. The global sections,
canonical first/second derivatives, smooth trace-free symmetric part and complete
four-term action are now native, with internal integrability and full polarization.
The actual meridional Hessian, rough Laplacian and all four density contractions
now give `Q(M_D(r))=2*pi*J_a[r]`, including the actual round value `8*pi/3`.
Genuine reflection orthogonality and parallel Hodge rotation now give the full
zonal sum `Q(M_D(r)+Z_D(s))=2*pi*(J_a[r]+J_a[s])`.
The actual normalized smooth Haar projection and complete four-term pairing/action
split are now native. Global smooth invariant-form classification and its exact
Haar/zonal action consumer are also native. Constructive trace/curl scalarization
of the same complete action is now native. Actual trace/curl scalar Haar
compatibility, zero angular means and pole vanishing for the original remainder
are native. The weighted endpoint/integrability and positive scalar estimate,
nonzonal positivity/equality, CK and separation remain open.
The complete analytic layer and current analytic manuscript passed scoped
independent Round 1 review at `2302ad1`.
The smooth profile/pole/metric producer and its manuscript claims passed Round 2
review at `76143bb`; the coordinate, curvature and volume layer and its manuscript
claims passed Round 3 review at `0a0b115`. The section/derivative/action layer
passed Round 4 review at `4cb46f6`; the meridional/zonal layer passed Round 5
review at `da1dd90`. The Haar projection/split layer passed Round 6 review
at `43111f9`.
The global invariant-form classification layer passed Round 7 review at `8765255`.
The new constructive scalarization and scalar Haar layers await independent review.
The full six-part suite below remains
mandatory; only coupled evolution and the exact unrestricted threshold value are
optional research frontiers.

## Conventions and fixed mathematical targets

The variational domain is the continuous functions on `[0,1]` taking values in
`[0, log C]`, for every real `C ≥ 1`. Lean uses real functions with `ContinuousOn`
on that interval, and equality/uniqueness must be restricted to the interval.
The functional is the Lebesgue integral of `2s exp(k(v)−k(s))` over
`0 ≤ v < s ≤ 1`. `pairFunctional_congr` ensures exterior values are irrelevant.

The geometric class consists of the actual smooth metrics on the unit two-sphere
produced by globally smooth positive balanced profiles `a : ℝ → ℝ`, together with
smooth diffeomorphic pullbacks of those metrics. No abstract circle-action
classification is assumed. The pole factors must be produced with their tying
equations, and actual covariant jets must come from the Levi-Civita connection.
There is no equatorial reflection hypothesis. Meridian reflection is a distinct
isometry used for the two zonal components.

| Mandatory headline | Exact intended conclusion | Native status |
|---|---|---|
| Haar decomposition and meridional reduction | For every metric in the stated class and smooth one-form, `Q(h)=Q(Ph)+Q(h−Ph)`, `Q(h−Ph)≥0` without pinching; actual smooth zonal forms satisfy `Q(M(r)+Z(s))=2π(J_a[r]+J_a[s])`. | Partial: exact zonal reduction, actual smooth Haar projection/complete split, global invariant classification, constructive original-action scalarization and actual trace/curl scalar Haar compatibility are native. The weighted endpoint/integrability and positive scalar estimate, nonzonal positivity and equality remain required. |
| All-cap optimum | For each `C≥1`, the specified continuous obstacle profile is admissible and minimizes the actual functional with value `2/3−β+1/(3β)`, where `q≥1` solves `log q+(2/3)(q³−1)=log C`, `α=(q⁴+2q)^(−1/2)`, `β=αq²`. | Native theorem and independent review complete, including the actual `C=1` value. |
| Rigidity | Equality in the optimal bound holds exactly for that profile on `[0,1]`; `C=1` is the constant zero logarithmic profile. | Native theorem and independent review complete, with both exact contact jumps and strictness for differentiable competitors at `C>1`. |
| Stability and near-symmetry | A positive explicit cap-dependent constant controls the squared `L²` distance; the two hemisphere deficits control reflection asymmetry without assuming symmetry. | Native explicit constant, actual variance identity, constant-mode anchor and all three full-interval consequences. Independent review passed. |
| Sharp CK geometry | `C_CK=((5+√13)/3)^(1/3) exp((4+2√13)/9)` is safe for every CK form in the stated metric class; every larger cap contains a genuine smooth negative witness with strictly smaller curvature ratio. At the safe endpoint, equality for smooth CK forms is precisely the zero form, subject to proving the new Haar equality bridge. | Open, including the equality bridge and the remaining geometric producers. |
| Structural separation | Plateau instability and valid geometric recovery give `C_rot<C_CK` for all one-forms in the same metric class, without a chosen rational intermediate cap. | Open. Exact unrestricted value is not claimed. |

The formulas and additional exact calculations appear in
[the calibration derivation](research/variational-calibration.md),
[the stability derivation](research/stability.md), and
[the geometric audit](research/geometry-audit.md). They are research records,
not by themselves established paper results. The new working manuscript includes
only claims mapped to native proofs. Its first geometric section proves smooth
balanced-profile pole factors, actual smooth positive sphere metric, cylinder pullback,
area, intrinsic curvature, global forms and canonical dissipation. Its exact
meridional/zonal reduction and intrinsic symmetry proofs are also present.
The smooth Haar projector, complete split and global smooth invariant-form
classification, constructive scalarization and scalar Haar compatibility are also
present. The remaining positive scalar estimate/nonzonal, CK, approximation and separation sections are still absent
as established claims.

## Shared dependency graph

```mermaid
flowchart TD
  P[Cap parameter: native] --> O[Admissible obstacle profile and contacts: native]
  D[Exact pair deficit and marginal: native] --> C[Explicit calibration and minimization: native]
  C --> OV[Exact optimal value: native]
  O --> C
  C --> R[Optimizer rigidity and contact regularity: native]
  E[Exponential quadratic remainder: native] --> S[Positive L2 stability: native]
  VAR[Weighted pair variance: native] --> S
  A[Obstacle anchoring: native] --> S
  C --> S
  S --> N[Two-hemisphere near-symmetry: native]
  G[Smooth metric and pole producers: native] --> H[Genuine Haar projection: native]
  G --> SEC[Global meridional and azimuthal sections: native]
  G --> CJ[Canonical metric covariant derivatives: native]
  CJ --> ACT[Complete action and polarization: native]
  CJ --> H
  G --> CV[Actual curvature, volume and cylinder coefficients: native]
  CV --> ACT
  CV --> J
  G --> MR[Exact meridional reduction: native]
  CV --> MR
  SEC --> MR
  ACT --> MR
  MR --> J[Full zonal reduction: native]
  ACT --> ISO[Diffeomorphism naturality: native]
  ISO --> ORTH[Meridian-reflection orthogonality: native]
  SEC --> ORTH
  G --> AREA[Actual parallel area form: native]
  AREA --> ROT[Hodge rotation commutation: native]
  ROT --> J
  ORTH --> J
  SEC --> J
  ACT --> J
  H --> HS[Full Haar pairing/action split: native]
  H --> IC[Global smooth invariant-form classification: native]
  HS --> Q[Nonnegative Haar remainder]
  ACT --> SC[Constructive trace/curl scalarization: native]
  AREA --> SC
  CJ --> GREEN[Canonical tensor integration by parts: native]
  CJ --> COMM[Surface covariant commutator: native]
  GREEN --> SC
  COMM --> SC
  SC --> Q
  H --> SH[Trace/curl scalar Haar compatibility and pole values: native]
  AREA --> SH
  SH --> Q
  ACT --> Q
  W[Positive scalar Haar gap] --> Z[Zero remainder iff zero form]
  W --> Q
  Q --> Z
  R --> CK[Sharp CK threshold and smooth equality]
  Z --> CK
  IC --> CK
  J --> CK
  C --> B[Box and balance preserving smooth approximation]
  B --> X[Smooth supercritical geometric witnesses]
  J --> X
  T[Plateau instability] --> TC[Moment-preserving curvature contraction]
  TC --> F[Area-coordinate exact-moment recovery in a strictly subcritical box]
  F --> SEP[Structural strict separation]
  C --> T
  J --> SEP
```

Each box has one mathematical role; shared nodes are not reimplemented per
headline. The analytic stability layer now uses actual interval means and primitives,
the full normalized lower-obstacle weight, and the true calibrated deficit. Its
general anchoring lemma derives every product's integrability from compact-interval
continuity. The next native frontier is the polar/angular positive estimate with
its weighted endpoint and integrability laws, and unconditional
remainder positivity/equality. The actual normalized projector, canonical
derivatives, full polarized split, global invariant classification and literal
original-action scalarization, scalar Haar compatibility and scalar pole values
are already available. Geometry proceeds through
real producers, not by moving the historical aggregate into the new project.

## Corrected conventions and load-bearing risks

- For a balanced reciprocal-curvature profile, `f(v)=2∫ᵥ¹ ξa(ξ)dξ`, `H=f/a`,
  `K=1/a`, and the exact hemisphere substitution is `k(v)=log(M/a(v))`.
  Using `log a` reverses the pair ratio. The southern identity uses balance.
- The constant-probe normalization is
  `J_a[c]=[2(I(k₊)+I(k₋))−4/3]c²`, and geometric half-dissipation is `2πJ`.
  The remaining native obligation here is the actual northern/southern
  hemisphere pair-functional substitution, including the southern balance identity.
- With area measured from the south pole,
  `f_K(x)=2x−2∫₀ˣ(x−s)K(s)ds`, hence `f_K''=−2K`, `f_K(0)=0`, `f_K'(0)=2`.
  On `[0,L]` the north-pole conditions require `∫K=2` and `∫sK=L`.
  Interior positivity also requires positive curvature: retain a bound
  `K≥kappa>0`, which makes the reconstructed warping strictly concave.
  The two moments alone do not imply positivity. Symmetry of the critical
  curvature profile is compatible with monotonicity on each hemisphere,
  not with global monotonicity of a nonconstant symmetric profile.
- The optimizer has derivative jumps at both contacts for `C>1`; the free arc
  collapses at `C=1`. Smooth nonattainment for constant probes alone cannot
  establish the full CK equality statement.
- A new positive scalar remainder is needed to prove
  `Q(h−Ph)=0 ↔ h−Ph=0`. The explicit polar square completion and proposed
  estimate with weight `1/b(z)` are recorded in the geometric audit, unproved
  in Lean. This is a genuine additional dependency, not an assumed equality law.
- General-probe action involves `a'`. Uniform approximation of `a` alone is
  insufficient for its convergence. Reconstruct the area-coordinate exact
  moment recovery and actual meridional action continuity instead.
- Critical-box recovery alone only gives a ratio at most `C_CK`. After proving
  negative action for a fixed smooth plateau probe, first contract the normalized
  curvature by `K_t=(1−t)K_*+2t`. Both exact moments are preserved. For `0<t<1`,
  the box `[L, L*C_CK]` contracts to `[lo_t, hi_t]` with
  `C_CK−hi_t/lo_t=2t(C_CK−1)/lo_t>0`. Actual action continuity must preserve
  negativity before smoothing inside this smaller box. This is a required native
  dependency, not an inference from critical-box recovery.
- No smooth attainment at the unrestricted endpoint has been established.
  Static negative dissipation proves neither coupled-flow existence nor CK
  preservation along a flow.

## Pinned foundation and source provenance

DG is released `v0.1.4`, revision
`788efe97894474c032de6dfb1289d515f613d15a`; Mathlib is revision
`c55e6e786f49471c72fbddbec5415808896aec1e`; Lean is `v4.35.0-rc3`.
The DG checkout was clean when inspected. The existing native cache passed the
initial root build. All 291 copied historical file hashes were checked against
the reference inventory; agreement authenticates reference bytes, not proofs.

The release's `convexOn_integral` and
`DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq`
were inspected directly. Neither substitutes for the weighted pair-variance and
constant-anchoring arguments required here. The optional parabolic infrastructure
has not been certified as a coupled Hodge-flow producer.

The parameter proof is new. The triangular functional and marginal method are
adapted from the owner's historical `PureRotationSharpThreshold.lean` and
`PureRotationSharpFunctional.lean`, retaining that attribution in the new source.
Those reference modules have no copyright/license header to copy. No historical
module or blanket linter disable is imported. New file headers preserve the
private project's absence of a license grant; the header linter remains enabled
with its expected license text configured accordingly.

The balanced-profile derivative and positivity arguments, pole-removal construction
and rank-one metric method adapt the owner's historical `BalancedRotationalProfile`,
`SmoothBalancedRotationalSphereMetric`, `RotationalSphereMetric` and
`BalancedRotationalSphereMetric` sources. The released DG Hadamard theorem replaces
the old quotient machinery. The metric construction uses current actual height
derivatives and ambient tangent orthogonality; it imports no historical aggregate.
