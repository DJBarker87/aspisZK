# R22 stage-2 focused proof packet

Branch: `codex/cx-overflow-s2-20261020`; source base `8ced75478`.
Status: **PARTIAL; R22 OPEN**. The function inventory and stopped targets are
in `../../design/OVERFLOW-FREEDOM-S2-20261020.md`.

The frozen verifier is intact: `freeze-source-check.json` verifies all 26
listed verifier/core source files. `type-correspondence.json` verifies the
retained type declarations equal generated declarations after removing only
imports, options, comments and blank lines. `body-pins.json` records 31 emitted
leaf bodies; `operation-census.json` lists local operations and accesses.
`backend-boundaries.json` is a lexical aid, not a verified call graph.

## Accepted focused results

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| R22Stage2LocalBodies | 0 | 7.08 | 2235367424 | 0 |
| R22Stage2ControlBounds | 0 | 2.31 | 2249916416 | 0 |
| R22Stage2LeafTotal | 0 | 15.42 | 2252521472 | 0 |
| R22Stage2ReaderTotal | 0 | 14.31 | 2245361664 | 0 |
| R22Stage2OpeningTotal | 0 | 21.22 | 2182774784 | 0 |
| R22Stage2Audit | 0 | 20.58 | 2204598272 | 0 |

The final audit reports 39 public theorems, each using only
`propext`, `Classical.choice`, `Quot.sound`. Layout equalities are actual
emitted bodies copied into a new module, with named checked scalar facts.
The opening accessor and two array accessors are actual complete bodies.
Control bounds are mathematical lemmas. The reader theorem is explicitly
parametric in unwrap; it is not the concrete Reader.raw theorem.

Every command, source hash/revision, direct dependency fingerprint, wall time,
RSS/swap metrics and full axiom output is in `manifest.json` and the per-attempt
receipts. The revision is the base plus the recorded source hashes: these
focused checks ran before the packet commit. No release replay was run.

## Rejected attempts and obstruction

Compiler diagnostics are retained, including local syntax/type errors and
layout proof replacements. No failed result is accepted through its printed
partial declarations. One concrete reader attempt exited 0 but used the
nonstandard `core.fmt.Formatter` axiom. The manifest rejects it explicitly.
The replacement source exposes unwrap and its on-Ok contract as parameters,
without editing Aeneas or any existing module.

The concrete whole generated emission imports missing `FunsExternal` (and
`TypesExternal`). Concrete decoder, field, pairing, iterator/allocation and
caller contracts remain unproved. Thus this packet does not claim totality
for resume, the multiproof loops, all 12 queries, or finish_relation. It does
not establish an admitted-input overflow counterexample either. Three
unrestricted-helper counterexamples and the corrected necessary premises are
recorded in the design report.

One wrapper's lock-directory cleanup encountered another writer's contents
after the compiler had exited; compiler exit and metrics are recorded
separately. No other job was killed and no shared object was overwritten.
The launchers use the mandated mkdir lock, exact Lean -j1 -M4400
-DElab.async=false, a separate object directory and the shared-process gate.

## Reuse

`check.py MODULE` compiles a single new module and refuses an unchanged
source+direct-import fingerprint. `summarize.py` validates current-source final
receipts, rejects nonstandard axioms and regenerates the manifest/theorem
index. `prepare.py` extracts source-pinned local bodies and the lexical census;
`layout-proofs.py` produces bottom-up constant proofs. The API probe is retained
only under `diagnostics/`.

All objects remain in `/tmp/codex-cx-overflow-s2-20261020-objects`; no binary,
object, archive, key, Rust/SBF artifact or root-level evidence is committed.
