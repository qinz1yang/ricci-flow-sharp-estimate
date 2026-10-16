# Native verification

From the repository root, using the pinned dependencies and toolchain:

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```

The script first builds the root aggregate, then elaborates each canonical source
with the repository options,
runs declaration checks, queries exact statements, and checks actual transitive
axiom closure. It hashes all project sources in this layer, the root aggregate,
manifest, toolchain declaration, build configuration and verification script,
and rejects a source change during the run. It verifies dependency revisions and
clean tracked dependency sources, and records the Lean executable hash. A prior
success receipt is removed before a new run. Temporary Lean drivers are created
outside project source and deleted afterward. The explicit selectors must contain
the relevant headlines and at least two hundred declarations. Actual audit counts
are recorded at the start of each axiom log, including private/generated declarations.

`unusedArguments`, `simpNF`, and `synTaut` run through Batteries' native linter
engine. This release has no registered `defLemma`; a native declaration-kind
inspection checks that definitions are not propositions and theorems are not
data. No linter is disabled. Syntax/style linters are enabled in ordinary
compilation. The expected header license text is configured for this private,
unlicensed project; all header checks remain active.

The optional `--reuse-receipt` argument reuses successful source elaborations only
when every prior project source, configuration, dependency revision, compiler hash
and semantic `-D` option still matches. Each reused output is verified and records
its prior receipt and hash. Original resource flags remain in the original recorded
commands; they are not semantic Lean options. The aggregate, declaration linters,
signatures and transitive-axiom audit always run again. New or changed source must
be elaborated afresh. Use a distinct output directory for each checkpoint.

The root aggregate is a real consumer of all 149 current modules. Importing it is required
before the evidence drivers. A cached root build does not replace fresh leaf
elaboration, and successful native validation does not replace independent
mathematical review of the statements.

The earlier checkpoint entries below retain their historical scope and evidence.
The final native and actual typesetting results are recorded in the Round16
entry at the end; earlier statements that typesetting had not run refer to
those preceding checkpoints.

The first canonical build exposed missing file headers that scratch compilation
had not reported: the release's header linter tests membership in the flat root
aggregate. Both headers were supplied and the canonical layer was rebuilt.
The mathematical proofs and signatures were unchanged by that repair.

The [first-layer evidence](evidence/round-0/receipt.json) passed independent review.
The [candidate-layer receipt](evidence/round-1-candidate/receipt.json) covers its six-module checkpoint.
The [calibration receipt](evidence/round-1-calibration/receipt.json) covers its nine-module checkpoint.
The final [Round 1 receipt](evidence/round-1/receipt.json),
[axiom closure](evidence/round-1/axioms.txt), and
[elaborated statements](evidence/round-1/signatures.txt) cover all thirteen modules.
The [stability receipt](evidence/continuation-2/receipt.json),
[axiom closure](evidence/continuation-2/axioms.txt), and
[elaborated statements](evidence/continuation-2/signatures.txt) cover all twenty-one modules,
including the actual weighted variance, obstacle anchor, explicit coercivity and hemisphere bounds.
The analytic layers passed scoped independent Round 1 review at `2302ad1`.
The [smooth metric receipt](evidence/round-2/receipt.json),
[axiom closure](evidence/round-2/axioms.txt), and
[elaborated statements](evidence/round-2/signatures.txt) cover all twenty-six modules,
including the smooth balanced-profile pole factors and actual sphere metric.
That producer layer passed scoped independent Round 2 review at `76143bb`.
The [coordinate/volume receipt](evidence/round-3/receipt.json) adds the actual
cylinder pullback, determinant/density laws and exact height integral. Its source
checks reuse the unchanged 26-module receipt and freshly elaborate the six new
modules; declaration and transitive-axiom checks cover the complete aggregate.
The [curvature receipt](evidence/round-3-curvature/receipt.json) extends this to
the exact cylinder range and the intrinsic scalar/sectional curvature of the same
metric on the whole sphere. It reuses the unchanged 32 source checks and freshly
checks the two final modules, root aggregate and all declaration/axiom/signature drivers.
Those coordinate/curvature/volume layers passed scoped Round 3 independent review
at `0a0b115`. The [section/action receipt](evidence/round-4/receipt.json) reuses
the unchanged 34 source elaborations and freshly checks five new modules. The root,
declaration/signature drivers and all 691 transitive axiom closures are checked
for the complete 39-module aggregate. That section, derivative and action layer
passed Round 4 independent review at `4cb46f6`.
The [meridional/symmetry receipt](evidence/round-5-meridional/receipt.json) checks
the complete 50-module aggregate and 1004 defining-module declarations. It reuses
the unchanged 34 source checks from the curvature receipt and freshly elaborates
the remaining sixteen sources, including the comment-only section-extension
attribution correction. The aggregate and all declaration, signature and actual
transitive-axiom drivers run again. The [final zonal receipt](evidence/round-5/receipt.json) extends
that checkpoint to 55 modules and 1083 defining-module declarations. It verifies
the unchanged fifty-source reuse chain, freshly elaborates the final five sources,
and reruns the aggregate and all declaration/signature/axiom drivers. The actual
Hodge rotation, first/second derivative and rough-trace commutation, all four
norm contractions and complete zonal `2*pi*(J[r]+J[s])` identity pass these gates.
The final receipt binds 60 source/configuration/checker inputs and 61 command
outputs. Both Round 5 layers passed independent mathematical and manuscript
review at `da1dd90`. Typesetting and the remaining whole-suite gates stay open.
The [Haar receipt](evidence/round-6/receipt.json) covers the complete 65-module
aggregate and all 1279 defining-module declarations. Its 55 reused source checks
are tied to unchanged accepted bytes; all ten new sources are freshly elaborated.
The aggregate, declaration linters, 232 required selectors, 329 signature queries
and actual transitive-axiom driver run at the new checkpoint. All source and
declaration outputs are silent. The receipt binds 70 inputs and 71 command outputs.
The five conventional Haar claims and exact map passed Round 6 independent review at `43111f9`.
The [invariant-classification receipt](evidence/round-7/receipt.json) extends this
to 72 modules, reusing 65 unchanged accepted source checks and freshly elaborating
seven new sources. The root and all declaration/signature/axiom drivers run again.
All 1433 defining-module declarations, including 553 private declarations, have
permitted transitive axioms only. All 260 required selectors and 357 signature
queries are covered; 77 inputs and 78 command outputs are fingerprinted.
Source and declaration-linter outputs are silent. Those four conventional claims
and their exact mapping passed Round 7 independent review at `8765255`.
The [scalarization receipt](evidence/round-8/receipt.json) covers 82 modules,
reusing 72 unchanged accepted source elaborations and freshly checking ten new
sources. The root and all declaration/signature/axiom drivers run again. The
1543 defining-module declarations include 620 private declarations; every
transitive closure has only permitted foundational axioms. All 291 required
selectors and 390 signature queries are covered. The receipt binds 87 inputs,
88 command outputs and three generated drivers; source and declaration outputs
are silent. The [scalar Haar receipt](evidence/round-8-haar-scalars/receipt.json)
extends this to 86 modules and 1609 declarations, including 626 private declarations,
with 323 required selectors and 422 signature queries. It reuses 82 unchanged
source elaborations and freshly checks four new modules; 91 inputs, 92 outputs
and three drivers are fingerprinted. Both layers and their nine conventional
claims passed Round 8 independent review at `659006b`. Historical receipts remain
unchanged; the earlier 388-query prose omitted two multiline signature commands.

The [positive scalar estimate receipt](evidence/round-9/receipt.json),
[axiom closure](evidence/round-9/axioms.txt), and
[exact signatures](evidence/round-9/signatures.txt) cover all 94 modules.
The 86 accepted source elaborations are reused with verified provenance, and
eight new sources are freshly elaborated. The aggregate and all declaration,
signature and transitive-axiom drivers run. All 1748 declarations, including
705 private declarations, have only permitted foundational axioms. All 363
required selectors and 462 signature queries are covered; 99 input hashes,
100 output hashes and three driver hashes bind the evidence. Source and
declaration-linter outputs are silent. The six conventional claims and their
exact mappings passed Round 9 independent review at `da47567`. The positive estimate retains the
original metric/differential/volume and derives every weighted integrability
condition internally.

The [original-remainder receipt](evidence/round-10/receipt.json),
[axiom closure](evidence/round-10/axioms.txt), and
[exact signatures](evidence/round-10/signatures.txt) cover all 98 modules.
It reuses 94 unchanged accepted source elaborations and freshly checks four new
sources, then reruns the aggregate and all declaration/signature/axiom drivers.
All 1777 declarations, including 716 private declarations, have permitted
transitive axioms only. All 378 required selectors and 477 signature queries
execute. The receipt binds 103 inputs, 104 outputs and three generated drivers;
source and declaration outputs are silent. The original remainder's unconditional
nonnegativity, equality exactly at zero remainder, and strict Haar/zonal consumers
are native. The four conventional claims and native evidence passed
Round 10 independent review at `0473a6a`.

The [produced CK safety receipt](evidence/round-11/receipt.json),
[axiom closure](evidence/round-11/axioms.txt), and
[exact signatures](evidence/round-11/signatures.txt) cover all 107 modules.
The 98 preceding mathematical sources are unchanged and their successful
elaborations are reused with the recorded provenance; nine new sources are
freshly elaborated. The root and declaration/signature/axiom drivers run again.
All 1867 defining-module declarations, including 730 private declarations,
have permitted transitive axioms only. All 435 required selectors and 534
signature queries execute. The receipt binds 112 inputs, 113 outputs and three
generated drivers. Source and declaration-linter outputs are silent.
The first gate stopped on three long lines in generated selector expressions;
splitting those lines and rerunning the gate resolved the diagnostics without
changing any theorem or disabling a linter.

The actual north/south hemisphere identities, invariant CK classification,
critical variational cap and produced-metric CK safety/equality are now native.
The public consumers use both profile bounds and actual Gauss-curvature bounds,
include zero Haar average and cap one, and prove positivity of the fixed unit
meridional probe. Seven conventional claims and their exact map passed
Round 11 independent review at `ae5dc91`. The [manuscript receipt](evidence/round-11/manuscript.json)
records 115 unique labels, 143 resolved references and one resolved citation;
its structural checks do not claim typesetting.

The [smooth recovery receipt](evidence/round-12/receipt.json),
[axiom closure](evidence/round-12/axioms.txt), and
[exact signatures](evidence/round-12/signatures.txt) cover all 114 modules.
All 107 preceding mathematical sources remain unchanged; their successful
elaborations are reused with verified provenance, and seven new sources receive
fresh elaborations. The root and declaration/signature/axiom drivers run again.
All 1904 defining-module declarations, including 735 private declarations,
have only the permitted foundational axioms. All 460 required selectors and
559 signature queries execute; 119 inputs, 120 outputs and three generated
drivers bind the final evidence. Source and declaration-linter logs are silent.

The layer proves normalized convolution with exact even box preservation,
quantitative uniform continuity of the actual warp-ratio integral, the exact
relaxed-profile value, genuine smooth metric recovery with D_n.a=a_n, and
convergence of the original complete unit-probe action. It produces smooth
negative CK witnesses below each prescribed larger cap and a critical sequence
of positive actions tending to zero with the fixed scalar probe r=1.
The geometric stability consumers preserve the exact action denominator,
reflection factor four and a separate zero-coefficient law.
Seven conventional claims and their mappings passed Round 12 independent
review at `58d5dbc`. The [Round 12 manuscript receipt](evidence/round-12/manuscript.json)
records 127 unique labels, 160 resolved references and one resolved citation;
balanced structure is not a typesetting certificate.

The [represented-class receipt](evidence/round-13/receipt.json),
[axiom closure](evidence/round-13/axioms.txt), and
[exact signatures](evidence/round-13/signatures.txt) cover all 123 modules.
All 114 preceding mathematical sources are unchanged; their successful source
elaborations are reused with matching provenance, and nine new sources are
freshly elaborated. The root and native declaration/signature/axiom drivers run
again. All 2031 defining-module declarations, including 739 private declarations,
have permitted foundational axioms only. All 554 required selectors and 653
signature queries execute. The receipt binds 128 inputs, 129 outputs and three
generated drivers; source and declaration-linter logs are silent.

The new layer constructs the actual conjugated circle and its literal normalized
all-slot derivative integral, transports canonical operators and the complete
pairing/action, and supplies full-class Haar/zonal/CK safety/equality/stability
consumers. The universal safe-cap set, quantified over every represented metric,
actual positive curvature box and original smooth CK form, is exactly
`[1,criticalCap]`; its actual supremum has the radical/exponential value.
The same existing supercritical witnesses and critical fixed-probe sequence are
embedded in the represented class through identity maps.
Seven conventional claims and their exact mappings passed Round 13 independent
review at `70f0557`, closing AC4 and AC5. The [Round 13 manuscript receipt](evidence/round-13/manuscript.json)
records 140 unique labels, 181 resolved references and one resolved citation.
Actual typesetting is not claimed.

The [normalized-area realization receipt](evidence/round-14/receipt.json),
[axiom closure](evidence/round-14/axioms.txt), and
[exact signatures](evidence/round-14/signatures.txt) cover all 131 modules.
All 123 preceding mathematical sources are unchanged and their successful
elaborations are reused with matching provenance. Eight new sources are
freshly elaborated; the root and declaration/signature/axiom drivers run again.
All 2140 defining-module declarations, including 747 private declarations,
have only the permitted foundational axioms. All 607 required selectors and
706 signature queries execute. The receipt binds 136 inputs, 137 outputs and
three generated drivers. Source and declaration-linter outputs are silent.

This layer proves actual normalized curvature primitives and their
positive-curvature moment geometry; a smooth physical interval inverse with
closed-endpoint derivative laws; the complete six-entry area action with real
integrability; actual profile/probe jets and curvature-derivative cancellation;
and a fully tied smooth realization with all coordinates, endpoints, inverse
laws, curvature and original Q=2*pi*A equations. The round K=2/unit-probe
consumer gives the actual value 8*pi/3.
The source simplifier's single wording suggestion was applied: the smooth
extension agrees on the closed interval, with no exterior germ claim.
The final source-bound gate was rerun after that comment-only edit; the earlier
candidate receipt is preserved in ignored Root scratch and is not final evidence.
Round14 independently accepts this native layer and six of its seven new
conventional claims. Round15 accepts QS7's correction of the seventh: its three
x-dependent tying equations are restricted to [0,1], while R=r∘X remains global.
No Lean change was needed. The [historical manuscript receipt](evidence/round-14/manuscript.json) records
152 unique labels, 197 resolved references and one resolved citation.
Actual typesetting is not claimed.

The [critical-area/plateau receipt](evidence/round-15/receipt.json),
[axiom closure](evidence/round-15/axioms.txt) and
[exact signatures](evidence/round-15/signatures.txt) cover 139 modules.
The eight new sources are freshly elaborated; all 131 preceding mathematical
sources are unchanged and reuse matching accepted source evidence. The root
and full declaration/signature/axiom drivers pass. All 2281 defining-module
declarations, including 754 private declarations, have only the permitted
foundational axioms. All 707 required selectors and 806 signature queries execute.
The receipt binds 144 inputs, 145 command outputs and three generated drivers;
source and declaration-linter outputs are empty. Execution, reuse guards and
validation semantics of the checker are unchanged.

The [Round15 manuscript receipt](evidence/round-15/manuscript.json) records
160 unique labels, 204 resolved references and one resolved citation, with
balanced braces and environments. Round15 independently accepts that native
layer, three new conventional claims and QS7. QS8's explicit global-continuity
qualification of the generic reciprocal lemma was corrected after that checkpoint
and accepted in Round 16 at `2bda267`. No typesetting was recorded
at the Round15 checkpoint.

The new critical-area layer uses a proof-independent clamped physical inverse
of the actual normalized reciprocal integral. Both moments, slope and warp
pullbacks and the complete unit-probe action follow from genuine calculus and
forward substitution. The actual critical optimizer has a positive plateau,
strict average bounds, hemisphere shape and derived zero action. Its full
plateau flux and first variation produce one fixed smooth negative area probe,
with explicit step size, actual derivatives, initial data and endpoint constancy.
The source simplifier requested no changes; its delta check also covers the
midpoint simp-normal-form repair found by the unsuppressed native gate.

The [final separation receipt](evidence/round-16/receipt.json),
[actual axiom closures](evidence/round-16/axioms.txt) and
[exact signatures](evidence/round-16/signatures.txt) cover 149 modules.
All 139 accepted preceding mathematical sources are unchanged and reuse matching
source evidence; ten new sources have fresh silent elaborations. The final root,
available unsuppressed declaration linters, native declaration-kind inspection,
signature and actual transitive-axiom drivers pass. All 2420 defining-module
declarations, including 800 private declarations, have only permitted foundational
axioms. All 775 required selectors and 874 signature queries execute. The receipt
binds 154 inputs, 155 command outputs and three generated drivers. Checker
execution/reuse/validation semantics are unchanged.

This layer closes strict contraction, symmetric monotone exact-moment recovery
in the identical box, L1/ae convergence of the entire fixed-probe action, the
tied smooth negative original-metric witness, all-form cap-one safety and the
actual unrestricted-supremum strict comparison. The source simplifier reviewed
all ten final modules and recommended no source changes. No mandatory native
mathematical headline remains unproved. Round 16 independently accepted this final
layer, its seven new conventional claims, QS8, exact mappings, final native evidence,
actual typesetting and private delivery at `2bda267`; all seven acceptance criteria
are met.

Actual typesetting passes with [Tectonic 0.17.0](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0).
The [47-page PDF](../paper/exponential_pair.pdf),
[typesetting receipt](evidence/round-16-manuscript-final/typesetting.json),
[engine output](evidence/round-16-manuscript-final/tex-output.txt) and
[losslessly compressed TeX log](evidence/round-16-manuscript-final/tex-log.txt.gz) bind the exact manuscript, engine binary,
command and PDF hashes. The final run has no warnings, overfull/underfull boxes
or unresolved references. Long displays were broken at mathematical boundaries;
paragraph line breaking was improved without suppressing diagnostics. The raw
TeX log's original bytes are retained in gzip, including whitespace emitted by
the engine; the receipt records both compressed and uncompressed hashes. Reproduce
with the recorded release binary:

```sh
rfse_tex_output="$(mktemp -d)"
tectonic --keep-logs --keep-intermediates --outdir "$rfse_tex_output" paper/exponential_pair.tex
```

The engine and its caches were installed only in Root's temporary task directory;
no Lean dependency or historical delivered receipt changed. Typesetting is not
mathematical acceptance. The final independent review and private delivery are
recorded separately in the round summary and [suite status](mathematical-status.md).
The accepted manuscript receipt is [here](evidence/round-16-manuscript-final/manuscript.json).
It also includes the opening clarification that the competitors and variational
functional are real-valued; the paper makes no such restriction on its later
maps or tensor integrals. The earlier Round16 native and manuscript receipts
remain unchanged at their original delivered revision.

Finalization synchronized acceptance-status prose without changing any Lean
source, native configuration, manuscript source or PDF. The requested regression
gate passed again, reusing all 149 unchanged source elaborations and freshly
running the root build, declaration linters, signatures and transitive-axiom
drivers. The latter three outputs are byte-identical to the accepted Round16
outputs. The [finalization record](evidence/finalize/verification.json) binds
these checks; the [updated manuscript/map receipt](evidence/finalize/manuscript.json)
binds the unchanged accepted manuscript and PDF to the documentation-only map
update. Historical receipts are preserved. The separate generic code-review
hook had no configured base branch; the completed Round16 independent
mathematical acceptance remains valid for the unchanged sources.


## Phase II, Round 0: smooth complete-action variation

Phase I remains COMPLETE at finalized revision `721fd81`; its accepted source,
paper and historical evidence are unchanged. Phase II remains OPEN. The three
new canonical modules are `AreaActionFactorization`, `AreaActionVariation` and
`AreaVariationGeometry`. Their 19 public theorems establish full-action
factorization, automatic pole flux, exact variation, the smooth zero-mode
stationarity equivalence, positive weighted normalization and original-metric
consumers. They do not determine the unrestricted sharp constant.

The [final native receipt](evidence/phase2-round-0-final/receipt.json) covers
152 modules, 157 source/configuration inputs and 158 command outputs. All 149
unchanged phase-I source elaborations are reused from the accepted Round16
receipt; the three new modules have fresh silent source elaborations. The root,
unsuppressed declaration linters, declaration-kind inspection, exact signatures
and actual transitive-axiom drivers pass. The audit covers 2,449 defining-module
declarations, including 801 private declarations, with only permitted
foundational axioms. There are 797 required selectors and 896 signature queries.

An initial signature driver failed the line-length source linter on one new
fully qualified query. Splitting that query, with no theorem-source change,
resolved it. The final gate above was rerun on the final unchanged native input
bytes. No diagnostic was suppressed. A source-only simplifier found no required
changes; its optional uncompiled proof shortening was left out of this frozen
packet. Its configured independent outer review subsequently passed at `cea7baa`.

The [preservation record](evidence/phase2-round-0-final/preservation.json)
records unchanged phase-I paper hashes, all 149 original modules and 2,325
historical workflow files, historical task, native receipt and dependency pins.
The new [research notes and exact native map](research/phase2-unrestricted.md)
state the fixed-geometry scope, original object bindings, historical-tool audit
limitations and next joint-variation obligation. No new phase-II manuscript or
phase-I typesetting run is claimed.


## Phase II, Round 1: curvature variation and normalized conditions

The unchanged Round 0 packet passed its configured outer review at `cea7baa`.
The full Phase-II goal remains OPEN. The new curvature packet proves actual
affine primitives and exact moments, the complete-density derivative, justified
Volterra switching pairing, curvature-dependent mass correction, actual unit-mass
normalization and the probe eigen-equation. Explicit box-and-moment parameter
sets give necessary one-sided and two-sided local-minimum conditions, with
closed support used for free variations. No optimizer or determining threshold
is asserted; exhaustive original-data normalization remains the next task.

The [native receipt](evidence/phase2-round-1/receipt.json), SHA256
`feb07235ba74195349f48cc61d94bc8436a3522c7310c3dc06d5b07473a4f826`, covers
158 modules, 163 native inputs and 164 outputs. All 152 accepted prior source
elaborations are reused with unchanged hashes; the six new modules have fresh
silent elaborations. The root build, unsuppressed declaration linters and native
declaration-kind inspection pass. There are 857 required selectors and 956
signature queries. Actual transitive axiom checks cover 2,542 declarations,
including 812 private declarations, with only subsets of `propext`,
`Classical.choice`, and `Quot.sound`.

An initial affected-leaf build reported one overlong proof line. It was wrapped
before the final source-bound native run. No proof statement, proof logic or
linter setting was changed for this repair. The source simplifier found no
required changes; one optional shortening of the normalized-path derivative
proof was not applied to the already frozen packet. The configured fresh outer
review of this packet subsequently passed at `38bdb31`, without repeating accepted reviews.

The mathematical sources added are `Analysis/VolterraPairing`,
`Analysis/AffineIntervalVariation`, `Geometry/AreaCurvaturePrimitives`,
`Geometry/AreaProbeRayleigh`, `Geometry/AreaCurvatureVariation`, and
`Geometry/AreaCurvatureOptimality`. The checker changes only extend module,
selector and signature inventories. No verification infrastructure was redesigned.
The [research notes and exact map](research/phase2-unrestricted.md) distinguish
proved directional calculus from the open original-data, compactness, selection,
global comparison, recovery and endpoint obligations. No paper bytes changed.


## Phase II, Round 2: exhaustive original-competitor reduction

Phase I remains COMPLETE. The accepted Round 0 and Round 1 packets retain their
outer acceptance. Round 2 supplies smooth normalized geometry from arbitrary
original pole data, every smooth probe's actual jets and complete action,
physical nonzero/mass equivalences and the original metric L² scale. One
representation and one normalization precede all form/curvature-box quantifiers
in the represented Haar/action theorem. Both scalar-safety transfer directions
retain the existing original safe-cap API. These reductions identify no new
safe cap or unrestricted sharp value; Phase II remains OPEN.

The [native receipt](evidence/phase2-round-2/receipt.json), SHA256
`40d45c57bcc06c574e47ed6842e7c283a466a71808bdf616e1962f761f5b57bb`, covers
164 modules, 169 native inputs and 170 command outputs. It reuses 158 unchanged
accepted source elaborations and freshly elaborates all six new canonical
modules silently. The root build, unsuppressed declaration linters and native
declaration-kind inspection pass. All 919 required selectors are present;
1,018 exact signature/declaration queries pass. Actual transitive axiom checks
cover 2,670 defining-module declarations, including 816 private declarations,
with only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The receipt and all input/output hashes were rechecked after the gate.

The six leaves are `Analysis/ClosedIntervalDerivatives`,
`Geometry/SmoothAreaNormalization`, `Geometry/PhysicalProbeNonzero`,
`Geometry/NormalizedAreaAction`, `Geometry/NormalizedAreaMass`, and
`Geometry/NormalizedAreaHaar`. The flat aggregate imports each. The checker
change only extends inventories; the validation process and pinned dependencies
are unchanged. An initial module split omitted the `Manifold` notation scope in
the mass module. Adding that scope repaired the integration error before the
final successful gate, with no statement change or diagnostic suppression.

Exact supplemental native checks cover arbitrary positive constant profiles,
constant and nonconstant probes, physical inverse/curvature normalization and
the public action consumer for arbitrary original data. Their command, source
and silent-output hashes are bound in the
[checkpoint record](evidence/phase2-round-2/checkpoint.json). The source simplifier
found no required repairs; optional declaration relocation and proof compression
were left out of the frozen native packet. This advisory is not independent
acceptance. The configured fresh outer review of Round 2 remains pending.

The [preservation record](evidence/phase2-round-2/preservation.json) verifies all
158 accepted prior modules, all 2,325 historical Phase-I workflow files, the
historical task, accepted TeX/PDF and dependency pins. No manuscript was edited
or typeset. The [research notes](research/phase2-unrestricted.md) retain the exact
remaining polar compactness, original critical-object application, full joint
recovery, determining selection, global comparison and sharpness/endpoint gates.


## Phase II, Round 2 continuation: direct original-form variational consumers

The exhaustive normalization checkpoint at `ba9dade` remains unchanged. Two new
leaves, `Geometry/NormalizedAreaVariation` and `Geometry/NormalizedAreaRayleigh`,
add six theorems for original geometric action derivatives, full smooth-direction
stationarity, represented pullback variation, and the literal physical quotient
with its inverse squared length factor. Nonzero original forms supply the mass
needed for quotient differentiation. Original fixed-geometry directional minima
imply the scalar eigen-equation by the accepted stationarity theorem. No joint
minimizer, compactness, new safe cap or determining value is asserted.

The [continuation native receipt](evidence/phase2-round-2-continuation/receipt.json),
SHA256 `4507a32fc5dc8028591cfc9cb954da2fcf2087c019c6e9b4bdf3a3f8b437922c`, passes for
166 modules: two fresh silent source elaborations and 164 matching prior native
elaborations reused. The latter include the six initial Round 2 leaves whose
single outer review remains pending. Root build, unsuppressed declaration
linters and native declaration-kind inspection pass. There are 925 selectors,
1,024 signature/declaration queries and 2,694 actual transitive axiom rows,
including 818 private declarations. Only subsets of `propext`, `Classical.choice`
and `Quot.sound` occur. All 171 native input and 172 output hashes, three diagnostic
driver hashes and the literal new signatures were checked against the final bytes.

Supplemental native checks prove the actual unit-probe geometric quotient is
1/c² for every positive constant profile c, and instantiate the derivative from
arbitrary original D,R,S with no compatibility premises. They compile silently;
the [checkpoint record](evidence/phase2-round-2-continuation/checkpoint.json) binds
the driver and output. Root shortened the local-minimum proof to reuse the
accepted scalar stationarity equivalence. The source simplifier found no required
changes; an optional import narrowing was not applied during the final gate.
No diagnostic suppression or new dependency pin was introduced.

The [preservation record](evidence/phase2-round-2-continuation/preservation.json)
verifies all 164 previous native sources, including the 158 previously accepted
modules, the Phase-I paper, historical task/workflow and pins. Prior native
receipts are unchanged. The same single configured Round 2 outer review remains
pending for the combined packet. Phase I is COMPLETE and Phase II remains OPEN.


## Phase II, Round 3: complete-action coercivity and both-pole mass control

Round 2's normalization and original-form variation packet passed its single
outer review at `734dd5b`. Round 3 proves uniform complete-action coercivity with
an explicit curvature-box-dependent mass correction, the resulting bounds on
the actual operator energy and ordinary square integral, and one uniform radius
for the sum of the weighted masses near both poles. The original curvature-ratio
restriction remains present in the cap-class consumers. Curvature continuity
and C² probe regularity suffice; no curvature derivative bound or artificial
probe endpoint condition is imposed. This is the T7 estimate checkpoint, not a
weak-domain, full limiting-action, recovery or sharp-constant theorem.

The [final native receipt](evidence/phase2-round-3/receipt.json), SHA256
`3d013f1ad272b777d2bec161df9ac64220ed4f9b8ee6172ec3d0c1880f1c3003`, passes for
171 modules. All five new canonical modules have fresh silent elaborations;
166 unchanged accepted elaborations are reused. Root build, unsuppressed
declaration linters and native declaration-kind inspection pass. There are
953 selectors, 1,052 signature/declaration queries and 2,740 actual transitive
axiom rows, including 825 private declarations. Only subsets of `propext`,
`Classical.choice` and `Quot.sound` occur. All 176 native inputs, 177 outputs,
three diagnostic-driver hashes and the new public signatures were rechecked.

The five leaves are `Analysis/ParabolicWeightedHardy`, `Geometry/AreaWarpBounds`,
`Geometry/AreaProbeEnergy`, `Geometry/AreaPolarMass`, and
`Geometry/AreaActionCoercivity`. They contribute 24 public theorems and four
actual functional/coefficient definitions. The checker changes only extend its
existing inventories; the validation policy and dependency pins are unchanged.

An initial root build found that the new finite-regularity operator-continuity
lemma shared a fully qualified name with an accepted smooth theorem. The repair
renamed only the new C² lemma to `meridionalOperator_continuous_of_contDiff_two`
and updated its new consumers/queries. Accepted source was preserved. A bounded
name search over all owned Lean sources found no remaining collision, and the
final root/source/linter/signature/axiom gate above passes. No diagnostic was
suppressed. The source simplifier found no required mathematical rewrite before
that integration rename; the rename changed no statement or proof logic.

Native consumer checks cover both pole-concentrating polynomial families for
every natural exponent and an entire varying sequence of curvatures, probes and
original ratio boxes with unit mass and a common action bound sharing one radius. The driver was replayed after the final
rename and compiles silently. Its command/source/output hashes are in the
[checkpoint record](evidence/phase2-round-3/checkpoint.json). Earlier exact rational
polynomial computations were exploratory stress tests, not theorem evidence.

The [preservation record](evidence/phase2-round-3/preservation.json) verifies all
166 accepted prior modules, all 149 Phase-I modules, all 2,325 historical workflow
files, the accepted paper, historical task and fixed pins. No paper was edited
or typeset. The single configured Round 3 outer review remains pending; prior
accepted reviews and evidence remain valid. Phase I is COMPLETE and Phase II is
OPEN, with the exact remaining weak-domain, polar limiting-action, recovery,
joint critical-object, determining/global and endpoint obligations recorded in
the [research notes](research/phase2-unrestricted.md).

## Phase-II Round 3 continuation: direct polar action control

The continuation native command under the Root cache-writer lock was:

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-3-continuation \
  --reuse-receipt docs/evidence/phase2-round-3/receipt.json
```

It passed for 175 modules, with four fresh silent source elaborations and 171
matching prior native elaborations reused. Those prior inputs include 166 accepted
modules and the five initial Round 3 modules still awaiting outer review. Root
build, unsuppressed declaration linters, native declaration-kind inspection,
966 required selectors and 1,065 signature/declaration queries pass. All 2,766
actual transitive axiom rows, including 831 private rows, contain only a subset
of `propext`, `Classical.choice`, `Quot.sound`. All 180 input hashes, 181 output
hashes and three reconstructed diagnostic-driver hashes match the final files.

Receipt SHA256: `a0a0cf17bc5d9e0849a0bb8d7c43cc47978cdc05ad32dc2822bf82625f37516c`.

Supplemental native consumers verify the exact round constant-probe remainder
`−4` at each pole, the C¹ remainder-continuity API and one common two-pole radius
for a varying normalized sequence with the actual curvature-ratio restriction.
The driver compiles silently. The source-only simplifier found no necessary
changes; its optional continuity-proof cleanup was left outside this packet.
The single configured Round 3 outer review remains pending for the combined
initial and continuation packet; no duplicate acceptance review was added.

[The checkpoint](evidence/phase2-round-3-continuation/checkpoint.json) binds the
documents, supplemental driver/output and advisory scope. [Preservation evidence](evidence/phase2-round-3-continuation/preservation.json)
confirms all 171 prior native sources, all 149 Phase-I sources, all 2,325 historical
workflow files, the accepted paper, historical/current task and dependency pins
remain unchanged. Phase I is COMPLETE. Phase II remains OPEN; no joint limit,
weak-domain theorem, lower semicontinuity, exhaustive recovery or sharp value is claimed.

## Phase-II Round 4: actual joint weak limits with unit physical mass

The single Round 3 outer review accepted the combined estimate packet at
`2778716def07872f759e551b74b1f4f25fb331e9`; that supersedes the pending-review
status in its historical creation records above. Round 4 consumes those estimates
to construct an actual weak-derivative domain and a joint subsequence retaining
the original curvature box/ratio, both exact moments and physical mass one.
Probes converge strongly in L², their first derivatives converge locally
uniformly, curvature converges against every L¹ test, and the actual primitives
converge uniformly. The literal weak action is integrable. Full-action lower
semicontinuity, unrestricted recovery and all sharp-constant gates remain open.

The final native command, under the Root cache-writer lock, was:

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4 \
  --reuse-receipt docs/evidence/phase2-round-3-continuation/receipt.json
```

The [native receipt](evidence/phase2-round-4/receipt.json), SHA256
`8416efcda8c74f311022ca7587dd633c96ebc31a18a3b1574e388717e2d062c5`, passes for
193 modules: 18 fresh silent source elaborations and 175 unchanged accepted
elaborations reused. Root build, unsuppressed declaration linters and native
declaration-kind inspection pass. The 1,043 required selectors, 1,144 signature
and declaration queries, and 2,902 actual transitive axiom rows (865 private)
pass. Every axiom row contains only a subset of `propext`, `Classical.choice`,
`Quot.sound`. All 198 input hashes, 199 output hashes and three reconstructed
diagnostic-driver hashes match. Physical modules, checker inventory and flat
aggregate imports agree. Source-command provenance was followed through 2,636
records across 24 receipts. The checker delta only extends inventories and queries.

The 18 leaves contribute 73 public theorems and four definitions. An initial
native declaration-kind failure on compiler-generated proof-valued constructors
was repaired by expressing the same weak-derivative conditions as conjunction
predicates with eight named theorem projections. The consumer conditions remain
the same; no checker exception was added. The final linter also removed one
unused `T2Space X` assumption from the general Ascoli helper. Default resource
settings suffice throughout the final source gate.

The source simplifier inspected the 18-leaf packet and the subsequent two-predicate
delta, finding no required changes. Optional proof compression was left outside
this checkpoint. The final unused-binder deletion is a native-linter integration
repair. This advisory is separate from the single configured Round 4 outer
mathematical review, which remains pending.

The [checkpoint record](evidence/phase2-round-4/checkpoint.json) binds the exact
documents and supplemental native consumers. They instantiate the joint producer
on arbitrary varying sequences and on the nonvacuous round class K=2, r=√3,
whose actual mass is one and complete action is four, and check smooth weak-graph
embedding with exact action agreement. The [preservation record](evidence/phase2-round-4/preservation.json)
confirms all 175 accepted sources, all 149 Phase-I sources, all 2,325 historical
workflow files, paper bytes, historical/current tasks and pins remain unchanged.
Phase I is COMPLETE; Phase II remains OPEN. No unrestricted sharp value is claimed.

## Phase-II Round 4 continuation: complete-action lower semicontinuity

The continuation constructs a joint normalized weak limit whose literal complete
action is at most the liminf of the **original** smooth sequence. It retains all
initial joint-limit constraints and adds identified weak limits of both positive
square factors. The two curvature-linear integrals converge through genuine
strong L¹ coefficients and bounded weak curvature pairing. No strong curvature,
full-remainder continuity or vanishing operator-energy tails are assumed.

The final Root command was:

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-continuation \
  --reuse-receipt docs/evidence/phase2-round-4/receipt.json
```

The [native receipt](evidence/phase2-round-4-continuation/receipt.json), SHA256
`44c9e26f09fa250057bbfcc0c7a4c90e26e88d1e88d01238c77269ae1631a022`, passes for
202 modules: nine fresh silent source elaborations and 193 matching prior native
elaborations reused. The latter include 175 accepted sources and the 18 initial
Round 4 leaves awaiting the same outer review. Root build, unsuppressed declaration
linters and native declaration-kind inspection pass. The 1,061 required selectors,
1,162 exact signature/declaration queries and 2,955 actual transitive axiom rows
(899 private) pass, using only subsets of `propext`, `Classical.choice`, `Quot.sound`.
All 207 input and 208 output hashes and three reconstructed diagnostic-driver
hashes match. Physical/checker/root inventories agree; source-command provenance
was followed through 2,838 records across 25 receipts. Validation code and pins
are unchanged; the checker delta only extends inventories and queries.

The nine new leaves contribute 18 public theorems. Root repaired candidate-level
notation and function-application elaboration issues with explicit typed terms
and removed one unreachable tactic; final native outputs are silent without
suppression or resource overrides. The nine-leaf source simplifier advisory found
no required change. Optional consolidation of an existing private estimate was
left outside this checkpoint. Its inspected source hashes match the final bytes.

Supplemental native consumers instantiate arbitrary varying original box/ratio
sequences and the exact round K=2, r=√3 class. The latter retains unit physical
mass, both moments, a physically nonzero limit and weak action at most four.
The driver compiles silently and its final source/output hashes are bound by the
[checkpoint record](evidence/phase2-round-4-continuation/checkpoint.json).
The [preservation record](evidence/phase2-round-4-continuation/preservation.json)
confirms all 193 prior native leaves, accepted sources/paper, all 2,325 historical
workflow files, tasks, pins and previous receipts are unchanged.

The single configured Round 4 outer review remains pending for the combined
initial and continuation packet. Unrestricted derivative-sensitive recovery,
joint critical-object production and every determining/global/sharpness/endpoint
gate remain active. Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 recovery: smooth original realizations

The final recovery producer starts from original smooth unit-mass sublevels. It
constructs their joint weak limit with the original-sequence full-action liminf
bound and a smooth geometric recovery sequence. Common convex weights preserve
both exact moments and the actual curvature ratio; all weighted probe derivatives
converge strongly. Relative warp control at both poles passes the entire action.
Literal positive normalization supplies unit mass and nonzero original forms.
The theorem concerns produced original smooth-sequence limits, not density for
arbitrary elements of the maximal weak graph.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-recovery \
  --reuse-receipt docs/evidence/phase2-round-4-continuation/receipt.json
```

The [native receipt](evidence/phase2-round-4-recovery/receipt.json), SHA256
`2efecd5b6db3153e13ea7ba219e2bb30f26c38f1e6723d3fcf34a371d534cf45`, passes for
212 modules. Ten new source elaborations are silent; 202 matching prior elaborations
are reused, including the 27 prior Round 4 leaves awaiting the same outer review.
Root build, declaration-kind inspection and all available declaration linters pass.
The 1,075 required selectors, 1,176 signature/declaration queries and 3,007 actual
transitive axiom rows (937 private) pass. Every row uses only a subset of `propext`,
`Classical.choice`, `Quot.sound`. All 217 input and 218 output hashes and all three
reconstructed driver hashes match. Physical modules, checker inventory and flat
root imports agree. Source-command provenance was followed through 3,050 records
across 26 receipts. The checker delta only extends inventories and queries.

The ten leaves add 14 public theorems. Final canonical source and linter outputs
are silent without suppression or resource overrides. Root repaired candidate
elaboration, explicit representative conversions and an ambiguous infinity notation
before the successful gate. The bounded ten-leaf source simplifier found no needed
change, and its frozen hashes match the final canonical bytes. This advisory is
separate from the single configured Round 4 outer mathematical review.

Supplemental native consumers exercise arbitrary varying original smooth sequences,
returning the tied unit-mass weak graph and original nonzero metric/form sequence
with full dissipation convergence. The exact round K=2, r=√3 sequence reaches this
same producer with mass one and action four. A generic equal-moment consumer checks
both endpoint warp equalities without symmetry. Driver, command and silent output
hashes are bound by the [checkpoint record](evidence/phase2-round-4-recovery/checkpoint.json).
The [preservation record](evidence/phase2-round-4-recovery/preservation.json) confirms
all 202 prior native leaves, 175 accepted leaves, 149 Phase-I leaves, all 2,325
historical workflow files, accepted paper, tasks, pins and prior evidence remain
unchanged. No new typesetting was performed.

The combined Round 4 packet still awaits its single outer review. The precise
variational domain and all variation/recovery bridges used next, a produced joint
critical object, determining selection, universal safety, smooth sharpness and
endpoint scope remain required. Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 minimum: actual joint attainment

The six new leaves construct a physically nonzero weak minimum over the stated
recoverable class for each C≥1, with action equal to the actual normalized smooth
meridional infimum. Smooth nonemptiness, finite lower bound and an actual minimizing
sequence are proved. Every smooth competitor embeds, and the class’s action recovery
is derived from its graph topology. Original geometric recovery and the physical
quotient comparison retain the exact same objects and area scale.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-minimum \
  --reuse-receipt docs/evidence/phase2-round-4-recovery/receipt.json
```

The [native receipt](evidence/phase2-round-4-minimum/receipt.json), SHA256
`073c47e22439030a239ab7c4f34e2eb880c308464edd804467d34a251670ba6b`, passes for
218 modules. Six fresh source elaborations are silent; 212 matching prior ones
are reused, including the 37 earlier Round 4 leaves awaiting the same outer review.
Root build, native declaration-kind inspection and all available declaration linters
pass. The 1,100 required selectors, 1,201 exact signature/declaration queries and
3,053 actual transitive axiom rows (948 private) pass. Every row contains only a
subset of propext, Classical.choice, Quot.sound. All 223 input/224 output hashes,
three reconstructed diagnostic-driver hashes and physical/checker/root inventories
match. Reuse provenance covers 3,268 source-command records across 27 receipts.
The checker delta only extends inventories and queries.

There are 21 new public theorems and four definitions. Final source and linter
outputs are silent without suppression or resource overrides. Root repaired
candidate-level scalar-Lp reduction, an explicit elementary round integral and a
cleared local hypothesis before the final gate. The source simplifier inspected
all six final source files and found no needed change; its source hashes match.
Its source-only advisory is not a duplicate mathematical acceptance review.

Supplemental native checks instantiate the actual minimum from a cap alone, exclude
zero physical mass, embed the nonvacuous round pair, and consume the geometric
recovery with original all-sphere boxes and nonzero forms. The arbitrary-original-data
quotient check obtains the area normalization from the accepted producer, rather
than assuming independent normalized data. Exact source/command/silent-output hashes
are in the [checkpoint record](evidence/phase2-round-4-minimum/checkpoint.json).
The [preservation record](evidence/phase2-round-4-minimum/preservation.json) confirms
all 212 prior native sources, accepted sources/paper, 2,325 historical workflow files,
tasks, pins and prior evidence remain unchanged. No typesetting occurred.

The chosen recoverable class does not assert maximal weak-graph density. Its actual
minimum does not imply smooth attainment, zero action, feasible-direction equations,
threshold selection or universal safety. Those required mathematical gates remain
active, and the combined Round 4 packet still awaits its single outer review.
Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 variation: actual-minimum weak probe equation

The new five-leaf packet proves genuine weak graph linearity, actual geometry
bounds from recoverability, full-density polarization/integrability and action/mass
polynomials. Normalized smooth probe perturbations are proved feasible in the same
class. The actual joint minimum therefore satisfies the complete weak equation for
every smooth direction, with its actual action as eigenvalue and no extra pole
condition. Curvature variations and threshold selection are not asserted.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-variation \
  --reuse-receipt docs/evidence/phase2-round-4-minimum/receipt.json
```

The [native receipt](evidence/phase2-round-4-variation/receipt.json), SHA256
`e102b147f60608766804336eb2383a26dea6c60709636f76e925f79e55f17e3a`, passes for
223 modules: five fresh silent source elaborations and 218 matching prior ones
reused, including the 43 previous Round 4 leaves awaiting the same outer review.
Root build, native declaration-kind inspection and all available declaration linters
pass. The 1,125 required selectors, 1,226 exact signature/declaration queries and
3,090 actual transitive axiom rows (959 private) pass with only subsets of propext,
Classical.choice, Quot.sound. All 228 input/229 output hashes, three reconstructed
driver hashes and physical/checker/root inventories match. Reuse provenance covers
3,491 source-command records across 28 receipts. Checker changes only extend
inventories and queries; no validation rule or dependency pin changes.

There are 23 new public theorems and two definitions. Root generalized the mass APIs
to their natural L² hypotheses, removing irrelevant weak-jet inputs. Candidate
function-representative elaboration, a local name shadow and zero-multiplication
simplifications were repaired before final silent checks. No source diagnostic
suppression or resource override was used. The five-source simplifier inspected
all final source bytes and found no needed change; it supplied a source advisory,
not an additional mathematical acceptance review.

Supplemental native consumers check literal negative pairing density at both round
poles, the need for the positive-mass guard, generic normalized perturbation closure,
and cap-only production of a nonzero unit-mass minimum satisfying the constant and
identity test-direction equations. These directions do not have compact support.
The [checkpoint record](evidence/phase2-round-4-variation/checkpoint.json) binds their
exact source, command and silent output. The [preservation record](evidence/phase2-round-4-variation/preservation.json)
confirms all 218 prior native sources, accepted sources/paper, 2,325 historical
workflow files, tasks, pins and prior receipts remain unchanged. No typesetting occurred.

The same configured Round 4 outer review is pending. Feasible curvature variations,
their mass derivative and multiplier qualification, determining selection, universal
safety, sharp smooth witnesses and exact endpoint scope remain required. The weak
probe equation is a necessary condition, not a sharp-value characterization.
Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 curvature: actual-minimum curvature inequality

Five new leaves prove integrable-curvature affine primitive/moment/mass laws,
original smooth curvature convexity with mixed positive ratio witnesses, the
complete weak cubic action derivative, and normalized curvature-segment closure
in the actual recoverable class. Positive physical mass is derived throughout
[0,1]. The cap-only producer now returns one nonzero unit-mass joint minimum
satisfying both its full smooth-probe equation and the complete mass-corrected
curvature inequality toward every admissible smooth comparison curvature.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-curvature \
  --reuse-receipt docs/evidence/phase2-round-4-variation/receipt.json
```

The [native receipt](evidence/phase2-round-4-curvature/receipt.json), SHA256
`e89236c9b33c11753c74ff158dfacb13b93528fe78f0c52c4121d3a35ff33e9c`, passes for
228 modules. Five fresh source elaborations are silent, and 223 matching prior
elaborations are reused. The root build, strict native declaration-kind inspection
and all available declaration linters pass. The 1,148 required selectors and
1,249 exact signature/declaration queries match the inspected source. All 3,149
actual transitive axiom rows, including 985 private rows, use only subsets of
propext, Classical.choice and Quot.sound. All 233 input/234 output hashes and
three reconstructed diagnostic-driver hashes match, as do physical/checker/root
inventories. Reuse provenance covers 3,719 source-command records across 29 receipts.
The checker delta only extends inventories and queries; pins and gates are unchanged.

There are 20 public theorems and three definitions. Exact cubic interpolation of
integrable physical densities justifies every derivative coefficient; no Kprime
potential or totalized-integral shortcut is used. Root removed the unnecessary
supplied-mass-positivity burden by proving positivity on the whole convex segment.
Candidate beta-redex rewriting and redundant tactic tails were repaired before
final silent checks, without changing accepted sources or resource policies.
The five-source simplifier found no needed change and recorded matching hashes.
Its source-only advisory is not an additional mathematical acceptance review.

Supplemental native checks use the smooth exact-moment comparison
`J(x)=x²−x+13/6` in the positive ratio-three box. At the round unit-mass probe
`sqrt(3)`, the literal mass derivative is `−1/60`, so both moments do not make
the normalization correction vanish. Further consumers use the entire convex
segment without a positivity premise and obtain a single nonzero unit-mass joint
minimum from C≥1 alone, simultaneously satisfying the identity probe equation
and the round-comparison curvature inequality. The [checkpoint record](evidence/phase2-round-4-curvature/checkpoint.json)
binds exact driver, command and silent output hashes.

The [preservation record](evidence/phase2-round-4-curvature/preservation.json)
confirms all 223 prior native leaves, 175 accepted leaves, 149 Phase-I leaves,
2,325 historical workflow files, accepted paper, tasks, pins and 3,871 tracked
evidence files remain unchanged. No typesetting occurred. The same configured
Round 4 outer review is pending for the combined 53-leaf packet.

Further nonsmooth comparison directions, valid weak adjoint/switching and multiplier
qualification, required regularity/path transfer, determining selection, universal
safety, sharp smooth witnesses and exact endpoint scope remain active mathematics.
These necessary conditions do not determine C_rot. Phase I remains COMPLETE;
Phase II remains OPEN.

## Phase-II Round 4 adjoint: weighted curvature pairing

Five new leaves give the actual joint weak minimum a genuine integrable curvature
adjoint. The warp coefficient is controlled with the parabolic weight supplied by the graph;
slope and direct coefficients are integrable themselves. Exact Green-kernel
identities bind the original moment-constrained primitive differences, and a
generic weighted Fubini theorem represents the complete mass-corrected variation.
The cap-only producer retains the original nonzero unit-mass minimum and full
probe equation, adding the adjoint inequality for every admissible smooth curvature.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-adjoint \
  --reuse-receipt docs/evidence/phase2-round-4-curvature/receipt.json
```

The [native receipt](evidence/phase2-round-4-adjoint/receipt.json), SHA256
`c96df771ddcc0772fdbd1a0391efe6eb8cf6a32029a979c4429d0e27287480c5`, passes for
233 modules. Five fresh source elaborations are silent, and 228 matching prior
elaborations are reused. Root build, strict declaration-kind inspection and all
available declaration linters pass. The 1,173 required selectors, 1,274 exact
signature/declaration queries and 3,196 actual transitive axiom rows (1,002 private)
pass with only subsets of propext, Classical.choice and Quot.sound. All 238 input/
239 output hashes and three reconstructed diagnostic-driver hashes match, as do
physical/checker/root inventories. Provenance covers 3,952 source-command records
through 30 receipts. Checker changes only extend inventories and queries.

There are 19 public theorems and six definitions. Root repaired candidate indicator
membership elaboration, deprecated branch-lemma names, line wrapping, reserved
lambda notation, local measure notation and pointwise function-expression matching
before the final silent gate. No accepted source or validation/resource policy was
changed. The bounded five-source simplifier found no required change and recorded
matching hashes; its advisory is not a second mathematical acceptance review.

Supplemental native checks prove that the generic weighted engine handles the
nonintegrable coefficient 1/x on (0,1): with weight x, kernel x*s and constant
test one, the actual pairing equals 1/2. They also check both endpoint values of
the Dirichlet kernel. The exact-moment curvature comparison x²−x+13/6 at K=2,
r=sqrt(3), has full action variation −2/5 and mass variation −1/60. Its corrected
variation at multiplier four is −1/3, and the new actual adjoint pairing has that
same value. A cap-only consumer obtains the nonzero unit-mass minimum with its
integrable adjoint and every smooth-comparison inequality. Exact source/command/
silent-output hashes are in the [checkpoint record](evidence/phase2-round-4-adjoint/checkpoint.json).
These rational values are regression data, not a threshold claim.

The [preservation record](evidence/phase2-round-4-adjoint/preservation.json)
confirms all 228 earlier native leaves, 175 accepted leaves, 149 Phase-I leaves,
2,325 historical workflow files, accepted paper, tasks, pins and 4,108 tracked
prior evidence files are unchanged. Compiler, platform and ten clean dependency
revisions match the previous receipt. No typesetting occurred. The same configured
Round 4 outer review remains pending for the combined 58-leaf packet.

Nonsymmetric measurable-curvature comparison recovery/closure, moment constraint
qualification, required regularity/interface/path laws and all determining,
universal-safety, smooth-sharpness and endpoint gates remain active. The adjoint
representation supplies necessary conditions and does not identify C_rot.
Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 nonsymmetric curvature recovery checkpoint

Six new leaves prove smooth exact-moment recovery of every bounded measurable
curvature in its original positive ratio box, then extend the actual joint
minimum's complete integrable-adjoint inequality to every such comparison.
The quantitative construction uses native smooth approximation, two fixed interior
bumps with a proved invertible moment matrix, contraction toward the mean, and
exact treatment of boundary means and degenerate boxes.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-nonsymmetric \
  --reuse-receipt docs/evidence/phase2-round-4-adjoint/receipt.json
```

The [native receipt](evidence/phase2-round-4-nonsymmetric/receipt.json), SHA256
`ed4fdb58fc9fb646987daa5f99f257ef383facac9db1b0355ae5b52b9a82cac0`, passes for
239 modules. Six fresh source elaborations are silent; 233 matching prior
elaborations are reused. Root build, strict declaration-kind inspection and all
available declaration linters pass. The 1,185 required selectors, 1,286 exact
signature/declaration queries and 3,228 actual transitive axiom rows (1,019 private)
contain only subsets of propext, Classical.choice and Quot.sound. All 244 input/
245 output hashes and three reconstructed diagnostic-driver hashes match; physical,
checker and flat-root inventories agree. Provenance covers 4,191 source-command
records through 31 receipts. Checker changes only extend inventories and queries.

The six leaves add 11 public theorems and one definition. Root repaired candidate
indicator-integral elaboration, a triangle-inequality name, explicit integrability
arguments and pointwise normalization before the final silent gate. No accepted
source, linter or resource policy was changed. The source simplifier recommended
no change and recorded matching final hashes; this advisory is not a second
independent acceptance review.

The supplemental native driver uses a nonsymmetric four-step curvature with
values 7/4, 11/4, 5/4 and 9/4 on consecutive quarters. It proves the actual moments
(2,1), the positive box [1,3], distinct reflected values, same-box smooth recovery,
and the produced nonzero unit-mass minimum's inequality against that measurable
comparison. It also verifies exact constant recovery for the degenerate box [2,2].
The final driver compiles silently. Exact source/command/output hashes appear in
the [checkpoint record](evidence/phase2-round-4-nonsymmetric/checkpoint.json).

The [preservation record](evidence/phase2-round-4-nonsymmetric/preservation.json)
confirms all 233 prior native leaves, 175 accepted leaves, 149 Phase-I leaves,
2,325 historical workflow files, accepted paper, tasks, pins and 4,350 tracked
prior evidence files remain unchanged. Compiler, platform and ten clean pinned
dependencies match the previous receipt. No typesetting occurred. All worker
leases are released; the single configured outer Round 4 review remains pending
for the combined 64-leaf packet.

Moment constraint qualification, any further weak-probe/normalized-pair closure
used, required regularity/interface/path laws and all determining, universal-safety,
smooth-sharpness and endpoint gates remain active. The theorem supplies necessary
conditions and does not identify C_rot. Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 genuine moment-multiplier checkpoint

Four new leaves prove actual two-moment constraint qualification, derive two
multipliers for the integrable linear curvature adjoint, and apply measurable
box complementarity to the produced physical joint minimum. Strict original
ratio witnesses are derived at every cap above one; cap one is handled by exact
a.e. roundness and the degenerate box. No multiplier or separating normal is
assumed by the cap-only theorem.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-multipliers \
  --reuse-receipt docs/evidence/phase2-round-4-nonsymmetric/receipt.json
```

The [native receipt](evidence/phase2-round-4-multipliers/receipt.json), SHA256
`c5f6ab3cd0fcff4ef9e2bf9b6e94df9d2970b6efd889c8b5ea852a6366c233dc`, passes for
243 modules. Four fresh source elaborations are silent; 239 matching prior
elaborations are reused. Root build, strict declaration-kind inspection and all
available declaration linters pass. The 1,191 required selectors, 1,292 exact
signature/declaration queries and 3,261 actual transitive axiom rows (1,042 private)
contain only subsets of propext, Classical.choice and Quot.sound. All 248 input/
249 output hashes and three reconstructed diagnostic-driver hashes match, and
physical/checker/root inventories agree. Provenance covers 4,434 source-command
records through 32 receipts. Checker changes only extend inventories and queries.

The four leaves add six public theorems and no definitions. Root repaired native
function-expression matching, explicit pointwise integrability arguments,
functional extensionality, deprecated branch names and minor source diagnostics
before the final silent gate. No mathematical hypothesis, accepted source,
validation policy or resource limit was changed. The bounded source simplifier
recommended no change and recorded matching final hashes; it is not an additional
acceptance review.

The supplemental driver proves constrained minimality for the affine cost W=x
and then uses the new engine to obtain multipliers with zero residual a.e. It also
checks the arbitrary-measure box equivalence on infinite counting measure and on
a zero measure with inconsistent endpoints, derives a strict original ratio box
for round curvature at cap two, and consumes the actual minimum producer at caps
one and three. The cap-one object is round a.e.; the cap-three object is physically
nonzero and has the derived multipliers/signs. The final driver is silent; its
source/command/output hashes are in the
[checkpoint record](evidence/phase2-round-4-multipliers/checkpoint.json).

The [preservation record](evidence/phase2-round-4-multipliers/preservation.json)
confirms all 239 prior native leaves, 175 accepted leaves, 149 Phase-I leaves,
2,325 historical workflow files, accepted paper, tasks, pins and 4,598 prior
tracked evidence files remain unchanged. Compiler, platform and ten clean pinned
dependencies match. No typesetting occurred; all worker leases are released.
The single configured outer Round 4 review remains pending for the combined
68-leaf packet across nine checkpoints.

Regularity and weak flux/interface/boundary laws, further weak-domain or original
path bridges actually used, and all determining, universal-safety, smooth-sharpness
and endpoint gates remain active. The a.e. signs do not establish a structural
family or global sufficiency. Phase I is COMPLETE; Phase II is OPEN.

## Phase-II Round 4 actual Euler-flux checkpoint

Three new leaves derive global L1 coefficients for the complete weak probe
Euler identity, reconstruct actual absolutely continuous flux primitives and
all four natural endpoint traces, and apply the result to the cap-only physical
joint minimum. The weighted operator is identified a.e. with the leading
primitive, giving a continuous interior representative after division by f².
No endpoint value of the probe or its first derivative is assumed.

```text
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-4-flux \
  --reuse-receipt docs/evidence/phase2-round-4-multipliers/receipt.json
```

The [native receipt](evidence/phase2-round-4-flux/receipt.json), SHA256
`4ab103adc7583565f403e93d26f64e4029c6830b71de285d2c7d8ac6984cc303`, passes for
246 modules. Three fresh source elaborations are silent; 243 matching prior
elaborations are reused. Root build, strict declaration-kind inspection and all
available declaration linters pass. The 1,201 required selectors, 1,302 exact
signature/declaration queries and 3,286 actual transitive axiom rows (1,055 private)
contain only subsets of propext, Classical.choice and Quot.sound. All 251 input/
252 output hashes and three reconstructed diagnostic-driver hashes match;
physical/checker/root inventories agree. Provenance covers 4,680 source-command
records through 33 receipts. Checker changes only extend inventories and queries.

The three leaves add five public theorems and five definitions. The generic
reconstruction source compiled unchanged from its source-only packet. Root
repaired coordinate-function normalization, redundant simplifications and one
long line in the physical layer before the final silent gate. No hypothesis,
accepted source, trust, linter or resource policy was weakened. The bounded
source simplifier recommended no change and recorded matching final hashes;
this advisory is not a second acceptance review.

The supplemental silent driver uses the actual round curvature K=2 and smooth
linear probe r=x−1/2 with mass multiplier 100. It verifies the complete coefficient
polynomials and the literal flux formulas
P=−2x−30x²+64x³−32x⁴ and A=20x²−80x³+100x⁴−40x⁵. Both fluxes vanish at both
poles although r has endpoint values −1/2,1/2 and derivative one at both poles.
These are exact regression data, not a sharp-threshold or minimizing-eigenvalue
claim. The driver also checks the generic singleton-interval case and consumes
the actual cap-three minimum with absolute continuity, natural flux poles and
continuous interior operator representative. Its exact source/command/output
hashes appear in the [checkpoint record](evidence/phase2-round-4-flux/checkpoint.json).

The [preservation record](evidence/phase2-round-4-flux/preservation.json) confirms
all 243 prior native leaves, 175 accepted leaves, 149 Phase-I leaves, 2,325 historical
workflow files, accepted paper, tasks, pins and 4,850 prior tracked evidence files
remain unchanged. Compiler, platform and ten clean pinned dependencies match.
No typesetting occurred; all leases are released. The single configured outer
Round 4 review remains pending for 71 new leaves across ten checkpoints.

Further coupled regularity, curvature/interface analysis, weak-domain and original
path bridges actually used, and every determining/global/sharpness/endpoint gate
remain active. The flux and representative conclusions do not identify C_rot.
Phase I is COMPLETE; Phase II is OPEN.

## Phase II, Round 5: recovery witness ties and complete Picone comparison

Round 4's single outer review at `a65205d` verified its 71 new leaves and native
provenance, while finding one localized omission of convergence-to-minimum facts
from two convenience recovery interfaces. Round 5 strengthens those conclusions
and adds five leaves with eight public theorems: tied weak graph multiplication,
normalized recoverable product probes, actual multiplicative stationarity, the
complete Picone identity and a conditional smooth all-probe lower bound. The
same actual weak minimum satisfies the integrable signed identity. This supplies
no determining cap, sign/nonvanishing theorem for that minimum, or global selection.

The final gate was run under the Root writer lock:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-5 \
  --reuse-receipt docs/evidence/phase2-round-4-recovery/receipt.json
```

The [native receipt](evidence/phase2-round-5/receipt.json), SHA256
`dbf0506b5711d5c8cb9d8d0a36bf3bb53349873ea3be678d5378f4299c09cd27`, passes for
251 modules, 256 inputs and 257 outputs. Thirty-nine source elaborations are fresh
and silent; 212 unchanged source elaborations are reused from the genuine earlier
recovery checkpoint. That is the last unchanged prefix before the two repaired
modules. The existing checker policy is unchanged; no reuse filter or weaker
validation rule was introduced. All post-prefix modules, including the changed
sources and their affected consumers, are freshly checked. The full root build
passes with no diagnostics.

The inventory, physical leaves and flat imports agree. All 1,209 required selectors
are present; 1,310 exact signature/declaration queries and 3,322 actual transitive
axiom rows, including 1,076 private rows, pass. Every axiom closure is a subset of
`propext`, `Classical.choice`, `Quot.sound`. All three available declaration linters
and the existing native declaration-kind inspection are active and silent.
Read-only reconstruction confirms all diagnostic-driver hashes, source/output
bindings and 3,301 source-command provenance records across 27 receipts on the
chosen unchanged-prefix chain. The other prior evidence remains preserved.

Two supplemental native drivers bind the public interface and the comparison's
precise scope. `SameMinimumRecovery` is silent: from the strengthened geometric
headline alone it extracts the four graph limits for the same normalized tail,
the original form and both jets, scalar curvature, nonzero forms and dissipation;
it applies the weak identity to that same displayed minimum. It also instantiates
the smooth all-probe certificate at K=2,r=1,λ=4. `RoundNodalDiagnostics` returns
only its requested two signatures and two actual approved axiom closures. It
proves the nodal λ=100 counterexample to an all-probe bound with only the natural
product sign, and the positive nonstationary affine counterexample to inferring
the operator sign from positivity. Exact commands/source/output hashes are in the
[checkpoint record](evidence/phase2-round-5/checkpoint.json). These diagnostics do
not claim that either test probe is a joint minimum or a zero mode.

The [preservation record](evidence/phase2-round-5/preservation.json) checks all 244
unchanged leaves of the 246-leaf parent and explicitly records the two requested
API changes. All 175 Round 3 leaves, all 149 Phase-I leaves, 2,325 historical
workflow files, 5,105 prior tracked evidence files, accepted paper bytes, both
TASK files and fixed dependency pins remain unchanged. Compiler, platform and
all ten dependency revisions match. No new typesetting was performed.

The seven-leaf source simplifier advisory recommended no changes; its source
hashes match final native inputs. It is not an acceptance review. The single
configured Round 5 outer review remains pending; unchanged Round 4 mathematical
acceptance is reused. Phase I is COMPLETE; Phase II is OPEN. All determining,
universal safety, smooth sharpness, endpoint and final manuscript gates remain
required.

## Phase II, Round 5 continuation: actual local system and physical maximum principle

Five new leaves and fifteen public theorems derive the local weak FTC, genuine
interior C¹ regularity, an exact interior-corner obstruction, the actual minimum's
coupled first-order system and the smooth meridional maximum principle at both
physical poles. The strict-source version supplies reference positivity for the
complete Picone certificate. It does not establish the actual minimum's operator
sign or global C² regularity, identify a cap, or replace the remaining global gates.

The final command, under the Root writer lock, was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-5-regularity \
  --reuse-receipt docs/evidence/phase2-round-5/receipt.json
```

The [receipt](evidence/phase2-round-5-regularity/receipt.json), SHA256
`79646cf0185b4b00af2546873ceb135da88bd2e9bf1444557982d7294deef895`, passes for
256 modules, 261 inputs and 262 outputs. All five fresh source elaborations are
silent; the 251 unchanged prior elaborations are reused. The full root build,
all available declaration linters and native declaration-kind inspection pass
without warnings or suppression. All 1,224 selectors, 1,325 exact signature/
declaration queries and 3,353 actual axiom rows, including 1,091 private rows,
pass. Every transitive closure contains only a subset of `propext`,
`Classical.choice`, `Quot.sound`. Read-only reconstruction verifies all native
source/output/driver bindings and 3,557 source-command records across 28 receipts
on the chosen native lineage. The checker policy is unchanged.

The supplemental `RegularityAndSignChecks` driver is silent. It consumes the
cap-only physical minimum producer and the same canonical coupled system; tests
local logarithmic FTC without a global pole-integrability hypothesis; combines a
smooth linear graph with nonexistence of any second weak graph for its absolute
value at an interior node; retains the allowed pole corner `|x|`; checks that a
zero source does not imply strict positivity; and instantiates the strict-source
round certificate at eigenvalue four. Exact command, source/output hashes and
capture provenance appear in the [checkpoint](evidence/phase2-round-5-regularity/checkpoint.json).
No test assumes a minimizing eigenvalue or a sign for the actual weak minimum.

The five-leaf source simplifier recommended no changes and its hashes match final
sources. It is not an acceptance review. All worker read leases are released;
Root alone wrote canonical sources, used writable caches and performed native/Git
operations. The single configured Round 5 outer review remains pending for the
combined initial and continuation packets; unchanged Round 4 review is reused.

The [preservation record](evidence/phase2-round-5-regularity/preservation.json)
verifies all 251 prior native leaves, all 175 Round 3 leaves, all 149 Phase-I
leaves, 2,325 historical workflow files and 5,365 prior tracked evidence files
unchanged. Accepted paper bytes, both TASKs, dependency pins, compiler/platform
and all ten dependency revisions match. No typesetting was performed. Phase I is
COMPLETE and Phase II remains OPEN, with every determining/global/sharpness/
endpoint and final research/manuscript gate still required.

## Phase II, Round 5 weak poles: actual zero traces and weak maximum principle

Four new leaves, five public theorems and one literal flux definition close the
weak-domain pole comparison step. The actual derivative flux f²p is absolutely
continuous with zero traces derived from weighted graph integrability. A bounded
smooth negative-value test gives interior r≥0 from a.e. weak operator q≤0. The
operator sign remains a premise; strict nonvanishing and determining global
safety are not conclusions.

The final command, under the Root writer lock, was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-5-weak-poles \
  --reuse-receipt docs/evidence/phase2-round-5-regularity/receipt.json
```

The [receipt](evidence/phase2-round-5-weak-poles/receipt.json), SHA256
`bc9be8017024a780dcd93655000ec2ff43dfb0c0a8de557103a90e5e9d07702c`, passes for
260 modules, 265 inputs and 266 outputs. Four fresh source elaborations are
silent; all 256 unchanged prior elaborations are reused. Root build, source and
declaration linters and native declaration-kind inspection pass. All 1,230
selectors, 1,331 exact signature/declaration queries and 3,369 actual transitive
axiom rows, including 1,100 private rows, pass with only subsets of `propext`,
`Classical.choice`, `Quot.sound`. Read-only reconstruction verifies source/output/
driver hashes and 3,817 source-command records across 29 receipts on the chosen
native lineage. The checker changes only inventories and queries.

The silent `WeakPoleChecks` driver consumes the actual cap-produced minimum,
retaining its own literal flux, mass, physical nonzero and conditional sign
consequence. It checks both reciprocal endpoint divergences, the unit-mass round
probe sqrt(10)x with nonzero derivatives at both poles, and a generic interior
comparison allowing a negative raw endpoint value. The last test prevents an
unwarranted endpoint sign conclusion for arbitrary weak representatives. Exact
command, source/output hashes and capture provenance are recorded in the
[checkpoint](evidence/phase2-round-5-weak-poles/checkpoint.json).

The four-leaf source simplifier recommended no changes; its hashes match final
sources. This is source advice, not an acceptance review. All worker leases are
released. The single configured Round 5 outer review remains pending for the
three changed packets; unchanged Round 4 acceptance is reused.

The [preservation record](evidence/phase2-round-5-weak-poles/preservation.json)
verifies all 256 prior native leaves, 175 Round 3 leaves, 149 Phase-I leaves,
2,325 historical workflow files and 5,630 prior tracked evidence files unchanged.
Accepted paper bytes, both TASKs, pins, compiler/platform and all ten dependency
revisions match. No typesetting was performed. Phase I is COMPLETE; Phase II is
OPEN. All determining, universal safety, sharp original smooth witness, endpoint
and final research/manuscript/review requirements remain active.

## Phase II, Round 5 strict-interior comparison

Two new leaves and two public theorems derive strict interior positivity from
nonnegativity, a weak divergence inequality and one positive point. The physical
consumer supplies that point from the same recoverable competitor's unit mass,
using its literal flux and actual positive interior warp. Nonpositive operator
source remains an explicit premise; it need not be strictly negative everywhere.
No pole value, global C² regularity or determining cap is asserted.

Under the Root writer lock, the final command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-5-strict-interior \
  --reuse-receipt docs/evidence/phase2-round-5-weak-poles/receipt.json
```

The [receipt](evidence/phase2-round-5-strict-interior/receipt.json), SHA256
`9b34001835a037737b1656593d56653b132ec35af731c44b9d5b628575303c93`, passes for
262 modules, 267 inputs and 268 outputs. Two fresh source elaborations are silent;
260 unchanged elaborations are reused. Root build, required source/declaration
linters and native declaration-kind inspection pass. All 1,232 selectors, 1,333
exact signature/declaration queries and 3,374 actual transitive axiom rows,
including 1,103 private rows, pass with only subsets of `propext`,
`Classical.choice`, `Quot.sound`. Read-only reconstruction verifies all source/
output/driver hashes and 4,079 source-command records across 30 receipts. The
checker policy is unchanged; only inventories and queries were extended.

The silent `StrongDomainChecks` driver consumes the cap-produced minimum and
returns conditional strict positivity of that same object. An exact original
normalized round quadratic has a nonpositive operator with a zero at the
midpoint, demonstrating the genuine non-strict source scope. Zero diffusion
and zero-probe tests check why the corresponding hypotheses matter. Exact
commands, final source/output hashes and capture provenance appear in the
[checkpoint](evidence/phase2-round-5-strict-interior/checkpoint.json).

The two-leaf source simplifier found no required changes and its hashes match
final inputs. This was source advice, not an acceptance review. All worker leases
are released. The same single configured Round 5 outer review remains pending
for all four packets; unchanged Round 4 acceptance is reused.

The [preservation record](evidence/phase2-round-5-strict-interior/preservation.json)
checks all 260 parent leaves, 175 Round 3/149 Phase-I leaves, 2,325 historical
workflow files and 5,899 prior tracked evidence files unchanged. Accepted paper
bytes, both TASKs, dependency pins, compiler/platform and all ten dependency
revisions match. No typesetting was performed. Phase I is COMPLETE; Phase II is
OPEN. Operator-sign production, all-probe quotient/endpoint coverage and every
determining/global/sharpness/attainment/final manuscript gate remain required.

## Phase II, Round 6 prerequisite checkpoint — orientation remains open

The two new leaves contain six public theorems about global sign symmetry and
the actual negative-cap regime. **They do not resolve the Round 6 operator-
orientation gate.** No joint-minimum counterexample or new one-sided operator
producer is certified by this checkpoint.

Under the Root writer lock, the final command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-6 \
  --reuse-receipt docs/evidence/phase2-round-5-strict-interior/receipt.json
```

The [receipt](evidence/phase2-round-6/receipt.json), SHA256
`d33ba34d212e99d25e08a1e8c3bb2e0547e67cf81201438f8a36ecf738857a04`, passes for
264 modules, 269 inputs and 270 outputs. Two fresh source elaborations are silent;
262 unchanged accepted elaborations are reused. Root build, required source and
declaration linters and native declaration-kind inspection pass. All 1,238
selectors, 1,339 exact signature/declaration queries and 3,382 actual transitive
axiom rows, including 1,105 private rows, use only subsets of `propext`,
`Classical.choice`, `Quot.sound`. Read-only reconstruction verifies source/output/
driver hashes and 4,343 source-command records across 31 receipts. Checker policy
is unchanged; only source inventories/selectors/queries are extended.

The silent `OrientationRegimeChecks` driver produces an actual negative joint
minimum for a cap between the original threshold and the CK threshold. It checks
the negated same minimum, its global minimizing inequality and all four strong
recovery limits to K,−r,−p,−z, together with complete-action convergence. It also
checks cap-one safety and a nonvacuous negated round competitor with positive
actual operator. None of these tests assumes or produces the missing one-sided
orientation of an actual minimum. Exact command/source/output/capture bindings
are in the [checkpoint](evidence/phase2-round-6/checkpoint.json).

The source simplifier recommends no changes to either final leaf; its hashes
match. This is source advice, not an acceptance review. The prerequisite-source
advisory leases are released. A further bounded sign investigation continues
on the fixed read-only snapshot. Source-only curvature and fixed-geometry investigations are explicitly
unverified research, not native theorem dependencies. No sourced axiom is used.
The single configured Round 6 outer review is pending for the new prerequisite
packet; the accepted Round 5 packet is preserved without a duplicate review.

The [preservation record](evidence/phase2-round-6/preservation.json) verifies all
262 accepted parent leaves, all 149 Phase-I leaves, 2,325 historical workflow
files and 6,170 prior evidence files unchanged. Accepted paper bytes, both TASKs,
pins, compiler/platform and all ten dependency revisions match. No typesetting
was performed. Phase I is COMPLETE; Phase II and the Round 6 sign gate remain
OPEN, with all original determining/global/sharpness/endpoint/final requirements
still active.

### Round 6 research-note continuation

The additional bounded kernel and joint-transport investigations returned no
actual-minimum orientation proof or counterexample. Their new calculations are
explicitly provisional research notes, with no new theorem/native acceptance
claim. All source-only research and simplifier leases are now released.

No Lean source, native checker, pin or prior evidence was changed for this note
continuation. Matching native evidence from the prerequisite checkpoint is reused;
no extra compiler, linter, axiom or typesetting run is claimed. Final note bindings
are in the [research-note record](evidence/phase2-round-6-research/checkpoint.json).
The mainline gate and the full Phase-II suite remain open.

### Round 6 coupled-investigation continuation

The coupled numerical search and full source-level Hessian calculation did not
resolve actual-minimum operator orientation. Thirty-six local searches passed
their numerical consistency checks, but provide no exact feasibility, global
minimum, pointwise-sign or threshold certificate. The full critical-cone weak
variation argument remains provisional.

Root separately ran `HessianDiagnostic.lean` in scratch under the writer lock,
using the pinned compiler and unsuppressed standard source-linter options. The
completed run (exec session 99760, exit 0) printed the three requested exact
signatures and actual axiom closures, with no warnings or errors. The closures
use only `propext`, `Classical.choice`, `Quot.sound`. Its pointwise symmetric
density increment, principal-form identity and strict positivity calculation
do not assert weak-path feasibility or operator orientation. This diagnostic
was not added to the canonical library; no new library theorem is counted.

The [coupled-investigation record](evidence/phase2-round-6-coupled/checkpoint.json)
binds the exact command, source/output hashes, numerical scripts/results and
final documentation. The [raw native output](evidence/phase2-round-6-coupled/hessian-diagnostic.txt)
is preserved. Bounded source simplifier advice found no required correction and
retained these scope limits; this is not acceptance review. All worker leases
are released, and the same single configured Round 6 outer review is pending.

All 269 native inputs still match the existing Round 6 receipt. No canonical
Lean source, checker, root import, dependency pin or historical receipt changed
in this continuation. Their matching full native evidence is reused without a
new project build, declaration-linter or project axiom run. No typesetting was
performed. The precise remaining critical-cone question is recorded for the
reviewer; the original Phase-II completion criteria are unchanged.

## Phase II, Round 7 endpoint producer

Three new leaves contain five public theorems: subthreshold safety, original
endpoint safety, exact-curvature-cap transport of recoverability, zero smooth
value at the original threshold, and an actual zero-action minimum with the
same four graph limits. No accepted parent leaf is edited. The changing-cap
proof retains the actual limiting box and proves real liminf boundedness before
using it. The same-pair recovery regression remains explicitly covered.

Under the Root writer lock, the completed native command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-7 \
  --reuse-receipt docs/evidence/phase2-round-6/receipt.json
```

The [receipt](evidence/phase2-round-7/receipt.json), SHA256
`34c392df8810e50792dec522b9b1f90a5ffd55e51bc4e8f95d5bd4a2d53fb8de`, passes for
267 modules, 272 inputs and 273 outputs. Three fresh source elaborations are
silent and 264 unchanged accepted elaborations are reused. Root build, source
and declaration linters and native declaration-kind inspection pass. The 1,243
required selectors, 1,344 exact queries and 3,393 actual transitive axiom rows,
including 1,111 private rows, use only subsets of `propext`, `Classical.choice`
and `Quot.sound`. Read-only reconstruction checks all input/output/driver hashes
and 4,610 source-command records across 32 receipts. Checker policy is unchanged
outside inventories and queries.

`EndpointMinimumChecks.lean` obtains the zero-action pair without a zero-value,
operator-sign, branch or free-region premise. It consumes the same quadruple's
stationarity, classical first probe derivative, canonical operator equality,
absolute continuity and natural pole traces of both Euler fluxes, their a.e.
derivative laws, and all four strong recovery limits. A round-class check covers
cap transport to one with a degenerate curvature box. The final completed run
(exec session 53557, exit 0) has empty stdout/stderr. Exact source/output/command
bindings are in the [checkpoint](evidence/phase2-round-7/checkpoint.json).

Bounded source simplifier advice recommends no changes, with all inspected
hashes matching. It is source advice, not acceptance review. All source-reader
leases are released. The single configured Round 7 outer review is pending;
accepted Round 6 mathematics is reused without duplicate review.

The [preservation record](evidence/phase2-round-7/preservation.json) verifies all
264 accepted parent leaves, 149 Phase-I leaves, 2,325 historical workflow files
and 6,446 prior evidence files unchanged. Accepted paper, both TASKs, pins,
compiler/platform and ten dependency revisions match. No typesetting occurred.
Phase I remains COMPLETE. Phase II remains OPEN: the endpoint producer gives
neither operator orientation nor a determining value or smooth attainment.

## Phase II, Round 8 strict gap and smooth witnesses

Two new leaves contain four public theorems and no definitions. They prove the
exact normalized round value four, the strict threshold gap above one, an
actual negative smooth scalar competitor at each superthreshold cap, and an
original represented metric/nonzero smooth form with negative dissipation and
ratio strictly below any prescribed larger cap. All 267 accepted parent leaves
remain unchanged. Round 7's single outer review at `df362be` is reused.

The completed saved native command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-8 \
  --reuse-receipt docs/evidence/phase2-round-7/receipt.json
```

The [receipt](evidence/phase2-round-8/receipt.json), SHA256
`47294dc55e3713aee639e9e3e87aa9a2ef5ba3a37b9564b8cac168af46ce87fa`, binds
269 modules, 274 inputs and 275 command outputs. Two fresh source elaborations
are silent; 267 matching accepted elaborations are reused. The recorded root
build, source/declaration linters and native declaration-kind inspection pass.
There are 1,247 required selectors, 1,348 exact queries and 3,400 actual
transitive axiom rows, including 1,113 private rows, all using only subsets of
`propext`, `Classical.choice`, `Quot.sound`.

After operational recovery, Root checked every source/output hash, reconstructed
the three diagnostic drivers, and verified 4,879 source-command provenance
records through 33 receipts. The current platform, compiler binary/version and
ten clean dependency revisions match. Checker policy differs from the accepted
parent only in module inventory, required selectors and exact signature queries.
The unchanged saved native gate was reused, not rerun or inferred from empty
logs without completion records.

Root additionally compiled `SharpGapMassChecks.lean` under
`.lake/rfse-root-writer.lock` with the pinned unsuppressed source-linter options.
The completed execution (session 68875, exit 0) has empty stdout/stderr. It
consumes the derived strict-cap premise for moment qualification on the same
zero-action minimum, and the original negative-witness producer with strict
ratio room, both inverse maps, actual jets, all-sphere curvature and same-metric
dissipation. It derives physical nonvanishing from the same unit mass and probe
equation, independently of negative dissipation. Source SHA256 is
`f44110023b3c948a7b6dfb5c58bcd0bebf5ce8ff335fc630e1d285849b3b4cf8`.
The [checkpoint](evidence/phase2-round-8/checkpoint.json) retains the exact
command and source/output bindings. The older saved consumer is preserved but
its lost completion record is not used as acceptance evidence.

Bounded source-simplifier advice recommended no changes to the canonical
leaves and proposed the adopted consumer mass check. It is not an acceptance
review. Research reports on inverse-source replacement and genuine joint
variations remain provisional: no sign theorem, component recovery theorem,
physical counterexample or negative feasible critical direction is claimed.
All worker read leases are released. The single configured Round 8 outer
review is pending.

The [preservation record](evidence/phase2-round-8/preservation.json) verifies
267 accepted parent leaves, 149 Phase-I leaves, 2,325 historical workflow files,
6,722 prior tracked evidence files, accepted paper bytes, both TASKs and pins.
No typesetting or Phase-I modification occurred. Phase I is COMPLETE; Phase II
is OPEN. The round's endpoint operator-sign objective remains unresolved, as
do determining selection, all-probe and cross-geometry comparison, original
smooth endpoint equality/attainment and final suite acceptance.

## Phase II, Round 9 first prerequisite checkpoint

Nine new leaves contain 21 public theorems and two definitions. Their natural
scope is the transformed zero-trace weak domain, uniform operator graph
estimates, finite-order extension/simple-pole division, physical Green quotient
regularity and a weighted pointwise bound. Smooth inversion and simultaneous
same-cap recovery are not asserted by this checkpoint.

Root ran the coherent native gate under the writer lock:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-9-prerequisites \
  --reuse-receipt docs/evidence/phase2-round-8/receipt.json
```

Receipt SHA256 is
`fd6bd3ba91fdc2232ec9f2d445678c253d24c8789a8272b8208021e99194250d`.
The gate covers 278 modules, 283 inputs and 284 successful command records;
nine fresh silent source elaborations, with 269 matching accepted elaborations
reused. Root, source/declaration linters and declaration-kind inspection
pass. There are 1,270 selectors, 1,371 exact queries and 3,442 actual transitive
axiom rows, including 1,128 private rows, using only permitted foundations.
Source/output/driver reconstruction and 5,157 source-command records through
34 receipts match. Checker policy changes are only inventories and queries.

`InversePrerequisiteChecks.lean` completed silently (Root exec session 79594,
exit 0), applying the new domain and equation to the same actual endpoint zero
minimum without a sign or supplied transformed boundary premise. It also
instantiates one-derivative pole regularity for the continuous corner source
|x-1/2|. Bounded source simplifier advice finds no required changes; it is not
acceptance review. Exact bindings are in the
[checkpoint](evidence/phase2-round-9-prerequisites/checkpoint.json).

All 269 parent leaves and previous evidence remain unchanged. Phase I's paper,
historical workflow and pins are preserved. No typesetting occurred. The single
configured Round 9 outer review remains pending. The inverse split, its parent
sign selection and the complete determining/global/smooth-endpoint goal remain
open and implementation continues beyond this prerequisite checkpoint.

## Phase II, Round 9 smooth-inverse checkpoint

Four further leaves add four public theorems and no definitions. The smooth
inverse includes both physical poles, nonnegative and zero sources, and physical
interval uniqueness. Stability controls all actual derivative coordinates;
graph completeness retains both weak identities and all three strong limits.

The native command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-9-inverse \
  --reuse-receipt docs/evidence/phase2-round-9-prerequisites/receipt.json
```

Receipt SHA256 is
`b2f8380f0c09f837fbcdd53e067073ee44c4755ad2c63f329b524f5981f7d589`.
All 282 modules pass, with 287 inputs/288 successful command records, four
fresh and 278 reused silent elaborations. Root, unsuppressed linters and native
declaration-kind inspection pass. The 1,274 selectors, 1,375 exact queries and
3,480 actual axiom rows (1,155 private) use only permitted foundations. The
read-only provenance audit matches 5,439 source-command records through 35 receipts.

The supplemental smooth-inverse consumer completed silently (Root session 95297,
exit 0), exercising the zero-source solution's physical uniqueness and the
nonnegative-source producer. The prior warning-containing scratch invocation
is not used as evidence. Source-simplifier advice recommends no changes; it
is not an acceptance review. Bindings appear in the
[checkpoint](evidence/phase2-round-9-inverse/checkpoint.json).

All 278 prior native leaves, 7,289 tracked evidence files, Phase-I paper/history,
both TASKs and pins remain unchanged. No typesetting occurred. The configured
outer review remains pending. Same-cap raw inverse recovery is still being
constructed, and no endpoint sign or threshold determination is claimed.

## Phase II, Round 9 final inverse-split checkpoint

Seven further public theorems in seven leaves complete the bounded raw inverse
split and its common same-cap recovery. Across Round 9, twenty new leaves add
32 public theorems and two definitions. The original 269 accepted leaves are
unchanged; no parent sign-selection or determining-value theorem is claimed.

The final native command was:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-9-split \
  --reuse-receipt docs/evidence/phase2-round-9-inverse/receipt.json
```

Receipt SHA256 is
`0c6589070c4387056c4c8d07b86ddd7f2922321d14be44414715cad830757e4a`.
All 289 modules pass, with 294 input hashes and 295 successful command/output
records. Seven fresh and 282 reused source elaborations are silent. The root,
unsuppressed source/declaration linters and native declaration-kind inspection
pass. The 1,281 required selectors, 1,382 exact queries and 3,538 actual axiom
rows (1,206 private) use only `propext`, `Classical.choice` and `Quot.sound`.
Driver reconstruction and 5,728 source-command records through 36 receipts
match. Checker policy AST agrees with accepted Round 8 outside inventories
and signature queries.

The first attempt stopped because two private axiom-row names ended in
`error`, matching the unchanged diagnostic substring check. The helpers were
renamed to `error_bound`; no mathematical statement, proof or checking policy
was weakened. Failed outputs are retained in Root scratch and are not relied
upon. The final affected/root build and full native gate pass.

`InverseSplitChecks.lean` completed silently against the final canonical imports
(Root session 85428, exit 0). It starts from the actual endpoint zero minimum,
retains its minimality and all three difference identities, consumes both
literal component source equations, derives positive sum mass, normalizes both
jets together, and extracts all four strong recovery limits and the complete
action limit for that normalized sum. A separate zero-source instantiation
uses the raw producer with no mass or source-nonzero premise. Its source SHA256
is `72c59a1a925891f09061b32e6729788d1a7dfaaa6b6dd085cb0bbcb18a4cf443`.
Bindings appear in the [checkpoint](evidence/phase2-round-9-split/checkpoint.json).

The source simplifier recommends no changes to this seven-leaf packet or its
consumer. All reader leases are released; the single configured outer review
remains pending. All 282 prior native leaves, 7,581 prior tracked evidence
files, 149 Phase-I leaves, 2,325 historical workflow files, the accepted paper,
both TASKs, compiler/dependencies and pins are preserved. No typesetting or
numerical search was used. Phase II remains open at the geometry-specific
action comparison, all-probe coverage, determination/global sufficiency,
original smooth endpoint classification and final acceptance gates.

## Phase II, Round 10 global-scale checkpoint

Three new leaves contain three public theorems and no definitions. The
accepted Round 9 source and evidence are unchanged. Root ran:

```sh
python3 scripts/check_native.py --output-dir docs/evidence/phase2-round-10-scale \
  --reuse-receipt docs/evidence/phase2-round-9-split/receipt.json
```

Receipt SHA256 is
`f51ac4f29dd2bdde58aa735ffd189bf1f7d6e841a539769b22a91c38db83ebc4`.
The 292-module gate passes with 297 inputs and 298 successful command/output
records, three fresh and 289 reused silent elaborations. Root, required
unsuppressed linters and native declaration-kind inspection pass. There are
1,284 required selectors, 1,385 exact signature queries and 3,578 actual axiom
rows, including 1,242 private rows, using only permitted foundations. Driver
reconstruction and 6,020 source-command records through 37 receipts match.

The source-bound `ScaleBalanceChecks.lean` consumer completed silently in Root's
recorded import overlay (session 43369, exit 0). It obtains the centered balance
for the same actual endpoint zero minimum and separately checks the complete
adjoint pairing 12-lambda for the unit-mass round probe. Source SHA256 is
`1e9b7ed5e738f4fb7845623abfaaedf07c3b67b1c31266d38842f1c117c96aed`.
The three relevant checked source imports match canonical bytes. The
[checkpoint](evidence/phase2-round-10-scale/checkpoint.json) binds this command,
source/output, source advice and final documents.

The bounded simplifier recommends no changes; it is not acceptance review.
All 289 accepted parent leaves, 149 Phase-I leaves, 7,880 prior tracked evidence
files, 2,325 historical workflow files, accepted paper, TASKs and pins are
preserved. The configured outer review is pending for the new packet. This
checkpoint does not close Round 10's complete-action selection objective;
work continues on the actual critical-direction route and all original gates.

## Phase II, Round 10 regular-curvature/free-interval checkpoint

The bounded continuation adds four leaves, five public theorems and no
public definitions. The native gate in
`docs/evidence/phase2-round-10-free/receipt.json` passes:

- 296 modules, 301 source/configuration/checker inputs and 302 successful
  command/output records; four fresh silent source elaborations and 292 reused.
- The changed/affected/root build and unsuppressed source/declaration linters
  pass. Native declaration-kind inspection remains enabled.
- 1,289 required selectors, 1,390 exact signature queries and 3,635 actual
  transitive axiom rows, including 1,285 private rows. Every closure uses only
  propext, Classical.choice and Quot.sound.
- Read-only literal-AST reconstruction matches all diagnostic drivers. Checker
  policy outside inventories/selectors/signature queries is unchanged. Reuse
  provenance matches 6,316 source-command records through 38 receipts.
- All 292 preceding native leaves, 289 accepted Round 9 leaves, 149 Phase-I
  leaves, 8,182 previously tracked evidence files, 2,325 historical workflow
  files, accepted paper bytes, both TASKs, pins, compiler and dependencies are
  preserved.

Receipt SHA256:
`ea1f4cdd007367125058149c62c429584ff9c585d04ab9b782445c6cc266762d`.
The supplemental `FreeIntervalChecks.lean` uses canonical imports to retain
one actual endpoint minimum, its original ratio box and newly produced free
interval, mass one, zero complete action, global minimality and all four
smooth-recovery limits. Its final source/output/command/completion bindings
are recorded in the [checkpoint](evidence/phase2-round-10-free/checkpoint.json).
Source simplifier advice is NO CHANGE, not an independent acceptance verdict.
The single configured outer review remains pending for the Round 10 delta.
The beta upper sign, threshold determination and every remaining original
mathematical/final gate remain open.

## Phase II, Round 11 bounded API delta

Round 10 review Q3 is implemented in exactly two Lean files. The weighted
Green theorem now derives source measurability from weighted integrability
using the positive interior parabolic weight; its curvature-control caller
no longer supplies the redundant premise. No theorem, definition, conclusion,
physical domain or recovery witness is added or replaced.

`docs/evidence/phase2-round-11/receipt.json` records a passing native gate:
296 modules, 301 inputs and 302 successful command/output records; four fresh
silent elaborations and 292 reused. The affected root build, unsuppressed
linters and declaration-kind inspection pass. All 1,289 required selectors,
1,390 exact signature queries and 3,635 actual axiom rows (1,285 private)
pass; closures use only propext, Classical.choice and Quot.sound.

Receipt SHA256:
`f45c7448efb4b37602759af3e9ad51667243593a61ace782bccd7cbc84c806d6`.
The exact native signature has only the weighted-integrability hypothesis.
Literal driver reconstruction and 6,316 source-command records through 38
receipts match. The checker is byte-identical to the reviewed parent. Its
existing reuse rule requires an entirely unchanged source prefix, so the
successful gate uses the scale checkpoint. The first attempt stopped at that
reuse precondition after a successful affected/root build; no failed receipt
is relied on and no policy was weakened.

All 294 other parent leaves, 289 accepted Round 9 leaves, 149 Phase-I leaves,
8,488 prior evidence files, 2,325 historical workflow files, accepted paper,
both TASKs, compiler, pins and dependencies remain unchanged. The canonical
same-endpoint consumer completes silently, retaining the original curvature,
free interval, unit mass, zero complete action, global minimality and all four
recovery limits. Its source SHA256 remains
`f17ab9f8b996b667d3a06f73fe5f9b996adff991c5550bf8c753ff6f0f15b71a`.
Completed command/output bindings and the NO CHANGE source-advice hashes are
in the [checkpoint](evidence/phase2-round-11/checkpoint.json).

This is a bounded API repair. The finite-comparison reports are provisional,
not native selection or refutation theorems. The round's mainline comparison,
the determining/global and smooth-endpoint requirements remain unresolved.
The single configured outer review will assess this delta; the unchanged
Round 10 mathematical review is retained.


## Phase II, Round 13 signed continuation and nodal sets

The four new leaves prove weak energy uniqueness, local triangular nodal
isolation, and nonvanishing of the actual signed minimizing state. They give
isolated interior probe zeros and a finite zero set on every compact subset of
the physical interior, with no source-sign or curvature-derivative premise.
The original endpoint producer is reused, rather than reconstructed.

The final native gate passes for 300 modules, 305 input bindings and 306
successful command/output records. Four source elaborations are fresh and
silent; 296 accepted source elaborations are reused. The affected root build,
all three available declaration linters and native declaration-kind inspection
pass. The gate checks 1,294 required selectors, 1,395 exact signature queries
and 3,661 actual transitive axiom rows, including 1,304 private rows. Every
closure uses only propext, Classical.choice and Quot.sound. Literal driver
reconstruction matches, and 6,616 source-command provenance records through
39 receipts are verified.

Receipt SHA256:
`380a89cab4fb7dfaf806c0c9ead55891d7722e0f2c7d25c19bbc50821ac286dd`.
The initial validation attempt rejected long new signature-query lines after
its mathematical checks passed. Namespace-open query formatting fixed that
failure; no failed receipt is accepted. The final gate also validates the
simplifier's replacement of one duplicate private helper by Mathlib's abs_sub.
Checker policy outside inventories, selectors and exact queries is unchanged.

The canonical endpoint consumer retains the same K,r,p,z, mass one, zero complete
action, global minimality and all four recovery limits, while exposing the new
signed-state and nodal conclusions. Its completed command/output bindings,
source advice, preservation and final document hashes are recorded in the
[checkpoint](evidence/phase2-round-13-nodal/checkpoint.json).

The configured single Round 13 outer reviewer remains responsible for
independent acceptance. No unchanged accepted theorem is re-reviewed. The
operator-sign and tested matrix-selection routes remain unresolved and parked;
compact interior nodal finiteness does not determine the threshold, control
all pole nodes, prove a finite switching structure or settle smooth endpoint
attainment. Phase I remains COMPLETE and Phase II OPEN.

## Phase II, Round 14 interior curvature-clamp traces

Eleven new leaves contain eighteen public theorems and two definitions. They
prove genuine double-trace cut recovery, simplicity of every interior node
of a zero-action joint minimum, complete adjoint regularity and the actual
same-box curvature-clamp traces. The doubly cancelling numerator case is
resolved by a forced second-order feedback limit. No operator sign is supplied.

The final native gate passes for 311 modules, 316 input bindings and 317
successful command/output records. Eleven source elaborations are fresh and
silent; all 300 accepted Round 13 elaborations are reused. The canonical root
build, unsuppressed declaration linters and native declaration-kind checks pass.
All 1,314 required selectors, 1,415 exact queries and 3,797 actual transitive
axiom rows, including 1,384 private rows, pass with only propext,
Classical.choice and Quot.sound. Literal driver hashes match; 6,927 source
provenance records through 40 receipts are verified.

Receipt SHA256:
`396481718ee80a365e922e20f49715b13624ce3c21fa3b1d31f6e12f8633e5ec`.
Checker policy is unchanged outside module, required-selector and exact-query
inventories. Source advice replaces one private interval helper by Mathlib's
ordConnected_Ioo.uIcc_subset; the final native evidence covers the integrated
proof bytes. No failed gate receipt is relied on.

The canonical endpoint consumer exits zero silently. It retains the displayed
K,r,p,z, unit mass, zero action, global minimality, full scale-balanced residual,
literal curvature clamp, both node traces and all four original recovery limits.
Its source hash is
`41b39d794db05898d246752cfd3c4f175edf012dfb07da12df692c2c16cd02b9`.
The [checkpoint](evidence/phase2-round-14-nodes/checkpoint.json) binds this
consumer, exact source/document hashes, advice and preservation.

All 300 parent leaves, 149 Phase-I leaves, 9,104 prior evidence files and 2,325
Phase-I workflow hashes are preserved. Both tasks, accepted paper, fixed pins,
compiler/platform/dependencies and the immutable tracker prefix are unchanged.
The single configured outer delta review remains pending; accepted unchanged
mathematics is not re-reviewed. Physical-pole control, determining selection,
universal sufficiency, original smooth endpoint classification and full
manuscript/final delivery remain open. Phase I is COMPLETE; Phase II is OPEN.

## Phase II, Round 15 actual polar integrability and traces

Eight new theorem leaves prove singular tail/head integral bounds, H1
endpoint quotient integrability, a genuine weighted-derivative criterion,
parabolic divergence integrability, and their application to the complete
Euler source and actual minimizing probe. The literal operator and p are
unweighted L1. The explicitly tied probe extension is AC on [0,1], has
derivative p in the interior, finite one-sided traces and a global bound.
Zero probe traces are allowed; no source sign or polar state bound is supplied.

The final native gate passes for 319 modules, 324 inputs and 325 successful
command/output records. Eight source elaborations are fresh and silent;
all 311 accepted Round 14 elaborations are reused. The canonical root build,
unsuppressed declaration linters and native declaration-kind checks pass.
All 1,322 required selectors, 1,423 exact queries and 3,853 actual transitive
axiom rows, including 1,417 private rows, pass with only propext,
Classical.choice and Quot.sound. Literal driver hashes match, and 7,246
source-command provenance records through 41 receipts are verified.

Receipt SHA256:
`de8cca382a2506e19fcefa0cb9ca681e677a7e1ebc8c146fc7c511b9045b1073`.
Checker policy outside modules/selectors/exact queries is unchanged. Source
advice replaces two elementary neighborhood proofs by Ioo_mem_nhdsGT/LT;
the final native gate validates the integrated bytes. No failed gate receipt
is used as evidence.

The canonical endpoint consumer exits zero silently, retaining the original
K,r,p,z, mass one, zero action, global minimum, full accepted scale-box/clamp
data and all four recovery limits alongside the new pole conclusions.
Its source SHA256 is
`7a53f49893e3b2370cabc43763120bf92543534b2fc2d1444267ca3a71dbfa17`.
The [checkpoint](evidence/phase2-round-15-poles/checkpoint.json) binds its
exact command/output, final source/docs, source advice and preservation.

All 311 accepted parent leaves, 149 Phase-I leaves, 9,425 prior evidence files,
2,325 Phase-I workflow hashes, both tasks, accepted paper, pins and compiler/
dependency/platform bindings are preserved. The immutable tracker prefix is
unchanged. The single configured outer delta review is pending. No boundedness
of p/q, curvature pole trace, total node count, determining constant, universal
new comparison or original smooth attainment is inferred. Phase I remains
COMPLETE; Phase II remains OPEN with all original final gates retained.


## Phase II, Round 16 weighted-state and regular-adjoint pole laws

Four new theorem leaves prove a tied zero-boundary AC extension criterion,
closed weighted Dirichlet-adjoint continuity, actual weighted-state zero pole
limits and complete canonical regular-adjoint pole values. The centered
residual laws hold for every fixed multiplier, so the same once-produced
scale multiplier is retained. Both zero probe-trace cases are covered. Q5
removes avoidable hr/hp from standalone operator L1 and updates its caller;
the physical probe-trace statement keeps its legitimate continuity inputs.

The final native gate passes for 323 modules, 328 input hashes and 329
successful command/output bindings. Twelve source elaborations are fresh and
silent, including the two Q5 files and the four new leaves; 311 accepted
Round 14 elaborations are reused. The reuse policy requires an unchanged
prior source prefix, so the six unchanged Round 15 leaves are also elaborated
in that affected checkpoint. Their accepted mathematical review is reused.
Root, unsuppressed declaration linters and native declaration-kind checks pass.
All 1,326 selectors, 1,427 exact queries and 3,874 actual transitive axiom rows,
including 1,434 private rows, use only propext, Classical.choice and Quot.sound.
Literal driver hashes and 7,250 source-command records through 41 provenance
receipts match. Checker policy outside inventories/selectors/queries is unchanged.

Receipt SHA256:
`d462cd13e7e8abf12c6047f41b6b02469acf778c7ebfec1dba93c9523a41181a`.
No failed gate receipt is relied on. Source advice simplifies the two endpoint
zero integrals and a private one-sided-continuity helper. Root adds the explicit
zero-function reduction required by the first canonical elaboration; the final
native gate covers all integrated bytes. The failed attempt is retained only
in Root scratch, not as accepted evidence or a failed mathematical route.

The canonical same-endpoint and Q5 minimal-input consumer exits zero silently.
Its source SHA256 is
`7ae340b5defce6b4fca4ebeeede390808e901b8255fb0614251f9916c518c2dc`.
It retains the identical K,r,p,z, mass one, zero action, global minimum, one
original scale box/multiplier, all residual/clamp/interior-node laws and all
four strong recovery limits alongside the new weighted-state and adjoint pole
laws. Q integrability is also checked without hr/hp. The
[checkpoint](evidence/phase2-round-16-adjoint-poles/checkpoint.json) binds final
source, four documents, the consumer, source advice and preservation.

All 317 unaffected parent leaves, all 149 Phase-I leaves and 9,754 prior native
evidence files are unchanged. Exactly two parent source changes implement Q5.
All 2,325 Phase-I workflow hashes, 142 pre-restart historical Round-file hashes,
both tasks, accepted paper, compiler/platform, ten dependencies and fixed pins
are preserved. The immutable tracker prefix and historical stop-state remain
unchanged. The single configured outer delta review is pending; no second
review of unchanged mathematics is requested. Cancelling pole-clamp ratios,
total nodes/contacts, determining selection, universal sufficiency, precise
original smooth endpoint equality and final full-suite closure remain open.
Phase I remains COMPLETE; Phase II remains OPEN.

## Phase II, Round 17 corrected states and complete polar derivative rate

Nine new leaves add twelve public theorems and no definitions. Genuine
corrected Euler fluxes yield inverse-square estimates and zero distance
quotients. Actual p and canonical q are bounded, the two corrected-q
coordinates have finite respective pole traces, and the complete centered
regular adjoint has the stated genuine derivative rate at both poles.
Zero probe traces are included. The curvature-primitive correction remains
explicit unless its probe trace vanishes; no curvature limit is assumed.

The final canonical gate passes for 332 modules, 337 input hashes
and 338 successful command/output bindings. All 9 fresh source elaborations
are silent; all 323 accepted parent elaborations are reused. Root build,
unsuppressed declaration linters and native declaration-kind inspection pass.
All 1,338 required selectors, 1,439 exact queries and 3,943 actual transitive
axiom rows, including 1,448 private rows, use only propext,
Classical.choice and Quot.sound. Literal driver hashes and
7,582 source-command records through 42 provenance receipts match.
Checker policy outside modules/selectors/exact queries is unchanged.

Receipt SHA256:
`6fcda3feeb3b504cfc003b9240ff862816879db26aadb174e41e3cba711bd48f`.
The source simplifier's two direct restricted-measure proof substitutions
preserve every signature and witness law; final native evidence covers the
integrated bytes. Advice is source-only and receives no acceptance credit.
No failed canonical gate receipt is relied on.

The canonical same-endpoint consumer exits zero silently. Its source SHA256 is
`6f1f6e8ef27f94f479eea283b629f5c48e816a959ad6f604dc6734bb121c723f`.
It retains the same K,r,p,z, unit physical mass, zero complete action, global
minimum, one chosen scale box/multiplier, full residual/clamp/interior-node
laws, older pole laws and all four strong recovery limits and action passage.
Trace constants from the state and rate statements are explicitly identified
by uniqueness, and the actual derivative rate uses that same chosen t. The
[checkpoint](evidence/phase2-round-17-polar-rates/checkpoint.json) binds final
sources, four documents, exact consumer command/output, Root statement audit,
source advice and preservation.

All 323 parent leaves, 149 Phase-I leaves and
10,087 prior evidence files remain unchanged. All
2,325 Phase-I workflow hashes, 142 pre-restart historical Round-file
hashes, both tasks, accepted paper, fixed pins and compiler/platform/ten pinned
dependencies are preserved. The immutable tracker prefix and historical
stop-state remain unchanged. Round 16's single outer delta review, including
Q5, passes at 7a3d0bf. Round 17's single configured outer delta review is
pending; no repeated review of unchanged mathematics is requested.

This is a necessary polar rate. Cancelling divided-clamp limits, any further
zero-trace rates or representative bridge actually used, determining selection,
independent universal sufficiency, exact original smooth endpoint equality and
all-form transfer, and final full-suite manuscript/evidence/delivery remain
open. Phase I remains COMPLETE; Phase II remains OPEN, with C_rot undetermined.

## Phase II, Round 18 actual nonzero-trace polar clamp selection

Five new leaves add ten public theorems and no definitions. Genuine endpoint
FTC and actual warp/curvature-average rates connect the complete accepted
derivative rate to nested averaging. A proved bounded-average contraction
selects the actual clipped factor-five limit at a cancelling nonzero-probe-
trace pole. Exact reflection gives the right sign. One common scale box and
multiplier retain every residual/node law; noncancelling saturation is included.
Zero-R poles remain outside the curvature-limit conclusion.

The final canonical gate passes for 337 modules, 342 current input hashes
and 343 successful command/output bindings. All five fresh source
elaborations are silent; 332 accepted parent elaborations are reused.
Root, all three available unsuppressed declaration linters and native
declaration-kind inspection pass. The 1,348 required selectors,
1,449 exact queries and 4,005 actual transitive axiom rows, including
1,468 private rows, use only propext, Classical.choice and Quot.sound.
All three literal driver hashes and 7,919 source-command records
through 43 receipts match. Checker policy outside module/selector/query
inventories is unchanged.

Receipt SHA256:
`61746e82349a9e9f2153c6d7336bf5cee4254176bfceecfd680269c6c89d5454`.
The source simplifier's two private EventuallyEq.symm substitutions preserve
all ten public statements and witness laws; final native evidence covers the
integrated bytes. Source advice is not an acceptance review. No failed
canonical evidence is relied on; repaired scratch diagnostics are not failed
mathematical routes.

The canonical same-endpoint consumer is silent and exits zero. Its source
SHA256 is `5381375ce83d9e6842763db5259ab0f4161ff92a53adcff255bda7d95ef717b1`.
It retains identical K,r,p,z, physical mass one, zero complete action, global
minimality, the same full scale box/multiplier/residual/node/pole package and
all four strong original graph recovery limits with complete-action passage.
No nonzero pole trace or curvature limit is supplied to the endpoint example.
The [checkpoint](evidence/phase2-round-18-polar-clamp/checkpoint.json) binds
final sources, four documents, the consumer, Root audit, source advice and
preservation.

All 332 parent leaves, 149 Phase-I leaves and 10,429 prior evidence
files remain unchanged. All 2,325 Phase-I workflow hashes, 142 pre-restart
historical Round bindings, both tasks, accepted paper bytes, fixed pins and
compiler/platform/ten clean dependency revisions are preserved. The immutable
tracker prefix and historical stop-state match. Q6's stale current Round15
review sentence is corrected in the ordinary documentation delta, with no
new mathematical review/build or mainline credit. Round17's single outer
review passes at e33c0e1. Round18's single configured outer delta review
passes at 1c779db; unchanged accepted mathematics/evidence are reused.

Phase I remains COMPLETE; Phase II remains OPEN and C_rot undetermined.
Zero-R rates and every further used domain/interface/representative/coverage
bridge, informative determination/selection, independent universal sufficiency,
original smooth endpoint equality/all-form transfer and final full-suite
manuscript/evidence/review/private delivery remain open.

## Phase II, Round 19 zero-trace leading rates and boundary uniqueness

Seven new leaves add eight public theorems and no definitions. Genuine
AC/FTC and full-source bounds produce the actual singular Volterra
inequalities. Their shrinking-envelope contraction excludes simultaneous
zero probe/canonical-operator traces at either physical pole. The genuine
derivative flux and actual first-order warp rate give ordinary q,p,r leading
limits at every zero R trace, with the nonzero q coefficient derived and the
right p sign negative. Exact reflection retains the complete action multiplier.

The final canonical gate passes for 344 physical/checker/root modules,
349 current input hashes and 350 successful command/output bindings.
All seven fresh source elaborations are silent; all 337 accepted parent
elaborations are reused. Root, all three available unsuppressed declaration
linters and native declaration-kind inspection pass. The 1,356 selectors,
1,457 exact queries and 4,072 actual transitive axiom rows, including
1,505 private rows, use only propext, Classical.choice and Quot.sound.
All eight new declarations occur in the exact-signature and axiom output.
All three reconstructed literal driver hashes and 8,263 source-command
records through 44 receipts match. Checker policy outside the module,
required-selector and exact-query inventories is unchanged.

Receipt SHA256:
`957b8b6523f3c589cd1679566142b030ec853714ca8ac7cf90562ed8bac37ebb`.
The source-only simplifier removes one duplicate private absolute-difference
helper and replaces its two uses by Mathlib's abs_sub. All eight public
statements and same-object witness laws are unchanged; final native evidence
covers the integrated bytes. Advice is not independent acceptance. The two
source-only worker candidates remain provisional records; their final Root
integration and import/elaboration repairs are covered by canonical evidence.
No failed development diagnostic is used as successful evidence or a failed
mathematical route.

The actual canonical endpoint consumer is silent and exits zero. Its source
SHA256 is `824f5183e5270b9752631a7ed891c8c9c18890079bd789e2a83047fc0e767c03`.
It calls the endpoint producer once and the accepted scale/node/nonzero-trace
pole producer once. The new zero-trace constants are identified with that
same package's corrected-q constants by uniqueness of limits. The identical
K,r,p,z, physical mass one, zero action, global minimality, full residual and
one chosen kappa,t, all accepted node/pole laws, all four original strong
graph recovery limits and complete-action convergence remain. No zero or
nonzero pole trace, boundary coefficient or curvature limit is supplied.
The [checkpoint](evidence/phase2-round-19-zero-traces/checkpoint.json) binds
final source, four documents, this consumer, Root audit, source advice and
preservation.

All 337 accepted parent leaves, 149 Phase-I leaves, 10,776 prior evidence
files, 2,325 Phase-I workflow hashes and 142 pre-restart historical Round-file
hashes remain unchanged. Both tasks, accepted paper bytes, immutable tracker
prefix, historical stop-state, fixed pins, compiler/platform and ten clean
dependency revisions are preserved. All worker/advice read leases are
released; workers ran no Lean/Lake and accessed no Root writable cache.
The single Round19 outer review passes its mathematical/evidence component
at b31dc1e. Its remaining Q7 API/affected-evidence gate is addressed by the
Round20 delta. The unchanged mathematical review is reused; no duplicate
acceptance review is claimed.

Phase I remains COMPLETE; Phase II remains OPEN and C_rot undetermined.
At that checkpoint, higher zero-R H/D cancellation rates and every further
used polar/interface/
representative/coverage bridge, informative determination/selection,
independent universal sufficiency, exact original smooth endpoint equality
and all-form transfer, and final full-suite manuscript/evidence/review/private
delivery remain required. No total node/contact count or smooth attainment
is claimed by this checkpoint.

## Phase II, Round 20 quadratic polar remainder and complete pole limits

Four new leaves contain five public theorems and no definitions. The actual
complete adjoint has essential second-derivative limit -3*q*²/4 at every
zero probe trace, with the derived q*!=0. Genuine endpoint FTC gives the
oriented quadratic remainder -3*q*²/8. The same D=2*f*r² has
D/d³ ->q*²/4>0 and the same probe is eventually nonzero. All lower-order
trace cases yield eventual equality of the literal boxed Kc to an obstacle;
double cancellation gives -H/D ->positive infinity and upper saturation.
Together with the accepted nonzero-R feedback, one actual minimum and one
box/multiplier have both Kc pole limits. The sufficient Euler-flux rate is
P/d ->0 from the accepted corrected fluxes; no new O(d²) theorem is claimed.

Q7 internalizes continuity derived from local AC in the generic singular-flux
engine and removes that public binder. Its sole physical caller is adapted
without changing the physical headline. This accompanying API repair gets
no separate mainline theorem credit. The exact revised signature and its
minimal-input external consumer supply no q-continuity premise.

The final gate covers 348 physical/checker/root modules, 353 input hashes
and 354 successful native command/output bindings. Eleven source
elaborations are fresh and silent; 337 accepted elaborations are reused.
The unchanged-prefix reuse origin is Round18, because Q7 changes two
Round19 leaves. Thus four unchanged Round19 Analysis leaves are freshly
elaborated along with the three affected Q7 leaves and four new leaves;
their accepted mathematical review is retained. The 1,361 required
selectors, 1,462 exact queries, unsuppressed declaration linters and native
declaration-kind inspection pass. All 4,132 actual transitive axiom rows,
including 1,546 private rows, use only propext, Classical.choice and
Quot.sound. The reconstructed literal diagnostic hashes and 8,267 source
command provenance records through 44 receipts match.

The [native receipt](evidence/phase2-round-20-polar-saturation/receipt.json)
has SHA256
`3c11e5db70ec509f6fa035f4b5f447c83efaa01eda4f4049908a94624c6586cc`.
Its execution provenance is explicit. The unchanged helper first reached
its 180s root-build limit; a serial Root prebuild then succeeded. Its next
run completed the root, 337 matched reused sources and ten fresh silent
sources before the combined source reached the same wall limit. No
successful helper entry point is claimed. The observed fail-fast prefix
is retained with its exact commands, raw bindings and explicitly inferred
zero exits: the helper aborts before the next command on any failed status
or forbidden diagnostic. Root then completed the remaining exact source
command and three literal drivers without that external wall timeout.
The receipt binds the partial-prefix record and continuation script. Lean
options, all diagnostic/axiom requirements and checker policy outside the
three inventories are unchanged. No duplicate RFSE compiler was launched;
these transport retries receive no mathematical route-failure credit.

The canonical AllPoleChecks consumer passes with empty output and source
SHA256 `976ddfe2b70a296dd8735b928c6c8c9090822e54c8510bf8a7ca73fcc5d305cf`.
It calls the actual endpoint producer once and the new pole producer once,
retaining identical K,r,p,z, unit mass, zero action, global minimality, one
kappa,t and full scale/residual/node/pole data, all four strong original
graph recovery limits and complete-action convergence. Its zero-R cases
include the derived leading coefficients, actual quadratic/cubic rates,
all saturation signs and doubly cancelling divergence. The Q7Checks
minimal-input consumer also passes silently, with source SHA256
`dcf483980047d1fe482780ac8280546e659ae6a494f6e9bcfef930307712eddf`.
Both import final canonical source/cache with no scratch overlay.

The source simplifier inspected one frozen read-only snapshot, with 9,352
input bindings, and proposed exactly two private field-cancellation
substitutions. All five new signatures, Q7's weakened signature and every
same-object equation are unchanged. The source-only worker packets and
advice are provisional; final Root native evidence covers the integrated
canonical bytes. Neither advice nor Root's semantic audit is independent
acceptance. All worker leases are released.

The [checkpoint](evidence/phase2-round-20-polar-saturation/checkpoint.json)
binds six final sources, four documents, both consumers, source advice,
Root's statement audit, native provenance and preservation. The only two
parent source edits implement Q7; 342 unaffected parent leaves, all 149
Phase-I leaves, 11,130 prior evidence files, 2,325 Phase-I workflow hashes
and 142 pre-restart historical Round-file hashes are preserved. Both tasks,
accepted paper bytes, fixed pins, compiler/platform and ten clean dependency
revisions remain. The immutable tracker prefix is unchanged.

The single configured Round20 outer delta review remains pending, covering
new mathematics and Q7 while reusing the accepted unchanged proof review.
Phase I remains COMPLETE; Phase II remains OPEN and C_rot undetermined.
The next principal test must confront a concrete determining/selection or
cross-geometry sufficiency implication. Every used domain/path/coverage/Haar/
recovery bridge, independent universal safety, exact original smooth
endpoint/all-form equality and final full-suite manuscript/evidence/review/
private delivery remains required. No total node/contact count, fixed
switching, symmetry, finite family, unique branch or smooth attainment is
claimed.
