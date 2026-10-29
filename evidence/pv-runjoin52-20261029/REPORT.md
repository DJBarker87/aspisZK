# Runjoin52 — separated circle source and neutral computations

Entry `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, head
`ef805d853cdd61a323b0fa3b3b0646d25828e065` (LOG D457).
IDs 65500–65599 only; 65597–65599 reserved for audits. 0 Kani.
No branch change, merge, reset or push.

**Target not established. Whole ledger rows removed: 0.**
Endpoint premises removed/added/weakened/changed: **0/0/0/0**.

## Checked scope

The collision design was recorded before writing new Lean source. Both authoritative
generated Types sources remain byte-identical, with no variant substitution
or co-import. See `COLLISION-BRIDGE.md`.

`CircleRawScalar52`, `CircleRawTower52`, `CircleRawSampler52` and
`CircleRawMap52` reify the owned computation over U32 pairs, nested pairs,
Bool error/row codes, and the original two Result layers. Their import
closures exclude both colliding Types modules. `CircleR72Raw52` does the same
for the EJR-selected R72 circle cone, preserving checked operations and r23/r24
branches. These are new proof-native definitions, not generated-source edits
or replacements for pinned source authority.

The owned side proves all scalar and tower transports, then the byte sampler,
map and both row-specific fallbacks. `CircleOwnedComplete52.complete` proves
the complete source circle sampler Result for every block and both rows,
with the neutral point encoding as output. No success, stored-point value,
canonicality or desired source-equivalence premise is assumed in that law.

The R72 side proves every operation transport through
`CircleR72Ops52.op39`, the complete OOD-circle Result, preserving both Rust
errors and outer failure/divergence. `op30` handles the guarded multiplication
by splitting eight named guards and transporting each bind symbolically.
The inversion addition chains remain opaque; bare inverse-function arguments
are transported with a named function-extensionality equality.

`CircleOwnedSelected52.source` proves the AL-selected op259 callback equals
the neutral selector's callback on every block and row. Its projection proof
is checked separately from the R72/model side.

`CircleInstalled52` now has a compatible import closure, but attempt 65596
rejects its subsequent dictionary projection rewrite. The entire module is
uncredited, including its locally printed candidate lemma. This is a proof
rewrite failure, not another import collision or a shipped-source counterexample.

These source-to-neutral transports do **not** prove equality of the two neutral
arithmetic computations on the produced canonical domain. The owned side
uses CT/wrapping arithmetic; R72 uses checked and guarded operations. Their
canonical mathematical comparison and the actual common-sample association
remain open. Draft neutral arithmetic laws have no credit without a passing
receipt.

## Retained work and boundaries

Complete the common-sample semantic/prepare association at the original
`toRP` completion: neutral circle mathematical meaning, framed messages,
stored fields, coefficient trace, domain/map_err and returned records. Then
prove the actual backend hinput producer through initialization,
`build_with_material` and commitment mutations. It remains step (2), not a
caller premise or step-(4) installation.

Only then FinishContext, both opening constructors, all 22 query appends,
six node multiproofs/indices and the ordered publication equation.
**No named RUNJOIN_PUBLISH_COMPACT ordered proof-byte theorem was produced.**
Step (4) was not started. Deployed op79/op254 and disclosed/observerOracle
installations remain explicit. No whole-row credit for V038, V045, V163,
V165, V167, V244, V258–V260 or V262.

All eight endpoint fields and the three TrustItems are unchanged. Observer,
simulator, coupling, bad/query events, guards, failure independence and
side-channel scope are retained. V370 and D381/D386 remain named. No new
machine-code credit. Frozen Rust/client diff from 82566acdfb is empty.
PV_RJDec_ and all PV_OWN* sources are unchanged. No wallet/account keys,
shared sources or caches, other worktree, Rust/client source, soundness file,
ELF, extraction or native differential was changed or run.

## Validation

Every compiler launch used the pinned private workspace/cache, one module
per scope, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean
-M7000. Admission required exit zero and allowed:true in the launch shell.
Two cgroup scan races refused unlaunched IDs 65527 and 65543; each was retried
under the same ID after the full 180-second cooldown. No limits were raised.
No unchanged failed source was recompiled. No full unchanged regression or
package-wide replay was run.

Per-attempt receipts, original hash-verified module logs, failed source Git
blobs, admission checks, source identity checks and separate audit closures
are retained here. Final totals and audit metrics follow below.

## Final totals and audit receipts

**100 attempts exhausted: 81 accepted / 19 rejected; 0 Kani.** All 81 accepted
new modules are covered by the three separate audit closures, with 245 unique
printed new names in the non-audit modules. There is no completed joint
source-to-security-model circle value bridge. The isolated source adapters
are never co-imported; the neutral audit excludes both generated Types modules.

Proof-source freeze: **8a63c292b145009f899fd5e93e5d772be1303881**.
Peak RSS over all scopes: **4,493,152,256 bytes**; swap zero.

| ID | Exact target | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 65597 | R1Z.PV_RunJoin_OwnedAudit52 | 0 | 1.77 | 2693378048 | 0 |
| 65598 | R1Z.PV_RunJoin_ModelAudit52 | 0 | 1.94 | 4493152256 | 0 |
| 65599 | R1Z.PV_RunJoin_NeutralAudit52 | 0 | 1.21 | 2691260416 | 0 |

All printed axiom sets are subsets of propext, Classical.choice and Quot.sound.
`audit-closure-check.json` verifies coverage and the import separation.
`new-source-credit-status.json` identifies the rejected installation module
and four uncompiled drafts (NeutralBase, NeutralScalar, NeutralAdd and the
OwnedTower aggregation interface). They carry no credit. Every lower-level
owned Op0–Op21 and all R72 Op0–Op40 modules are accepted.

All 19 rejected revisions are retained as hash-verified Git blobs.
`original-module-logs.json.xz` retains all 100 original outputs and time logs,
checked against receipt hashes. `admission-launch-audit.json` confirms zero
void launches and full cooldown compliance. `SUMMARY.json`, `commits.txt`,
the source-identity records and OPENING-NEXT.md provide the tally and next
consumer. The final evidence-only commit follows the generated commit list.

Historical stage-A reuse retains its existing source scope, deployed
features/profile/ABI, compiler-cohort, D188, allocation/TLS/filesystem,
Drop/unwind and K-1/K-2 qualifications. No source, native or machine-code
credit is enlarged by these new Lean transports.

Final cache preflight: **3,369** project source/object pairs, **7,426** direct
dependency fingerprints, **5,673** external objects and **5,438** IR companions,
all matching. See `final-preflight.json.xz` and its uncompressed SHA sidecar.
Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35; pinned
LEAN_PATH unchanged. Own running scopes: zero. `scope-sequence.json` verifies
nonoverlapping submissions. Regeneration leaves all 86 current source files
byte-identical (`generator-check.json`), including the explicitly uncredited
drafts. No full manifest is claimed as replayed.
