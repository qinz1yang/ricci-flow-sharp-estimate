# Round 25 source-only simplifier advice

One minimal worthwhile simplification is proposed in `FreeCharacteristicProbe.lean`; NO CHANGE is proposed for `QuadraticFluxProbe.lean` or the scope notes.

In `actual_free_interval_excludes_tight_field`, construct the existing `hgood` directly with `ae_restrict_of_ae_restrict_of_subset hsub (hK.and hsat)`. This standard restriction lemma removes the local `hrestrict` equality and the intervening doubly restricted-measure proposition. The exact `hgood` type remains unchanged, on `μ = volume.restrict (Ioo A B)`, with both strict-margin input data and the explicitly assumed a.e. remainder-saturation equation. Every theorem signature, coefficient definition, original primitive/probe binding and proof scope is unchanged. `simplification.patch` contains only this local substitution. It has not been compiled.

No concrete scope mismatch was noticed in the two private probes or their notes. `QuadraticFluxProbe` retains the literal complete density, actual jets and genuine geometry-state chain rule. `FreeCharacteristicProbe` excludes the extra whole-state tight Bellman specification with explicit remainder saturation at the same selected box. It does not derive saturation from zero action, exclude slack/nonquadratic certificates, prove unsafety, produce C_rot or settle endpoints. The positive global sharp producer remains unproved. This observation is bounded source advice, not independent mathematical acceptance.

Global AGENTS.md was read in full, and all five frozen inputs were read. Relevant lessons retained: qualified-name-search (no new names or public API), recovery-limit-witness-ties (no same-object/saturation equation erased), and flat-root-header (private probes are not promoted to canonical delivery; Root owns the applicable final gates). No new comparison, field construction or second acceptance review was attempted.

## Frozen input hashes

All five hashes match `inputs.json`; they were checked before and after source inspection:

- `QuadraticFluxProbe.lean`: `4d403b065f6aaf80610188f6c9a56f112bc83ad8cdc91b29310646085d9618fd`
- `FreeCharacteristicProbe.lean`: `0337cbb2fb9b51f260762c9ee09cc7a12ad3fec60debfdeb7197fa8ab4719296`
- `attempts.md`: `528a6e852a97aaa34793c0e0f7d18b6bd63c98d0d5709fe438e96678514af82a`
- `contract.md`: `d9316ed1757bc240696a8f6cf0ffce160e3cd002fbb3fd8378e6286e6a929738`
- `bitlesson.md`: `48215551a10642e35fca9e2bcbb8dfa5fba713b266a62d43c5721903e1e83855`

Manifest SHA256: `8c097ef058d96820137aa4e081dff6c6394d7b6fb8739733ef0ea82b0deef729`.
Patch SHA256: `a0949b3a5ade34d3b888f134ae1f9e547d08c62d1ecf7d1cdc1eebe45f8be7df`.

Status: PROVISIONAL source-only suggestion. No compiler/Lean/Lake, type, linter or axiom evidence is claimed and no acceptance verdict is given. Root alone integrates and performs native validation; the configured Astra/max outer reviewer remains separate. No inputs, receiving/canonical source, Git/cache, other scratch or snapshot were modified or copied; no network or descendants were used. No unavailable full-snapshot manifest was reconstructed.

Report and patch frozen after this write. Assignment and snapshot lease released: no processes or descendants remain, and no further accesses or edits are planned.
