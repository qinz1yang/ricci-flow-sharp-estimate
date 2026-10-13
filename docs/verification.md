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
