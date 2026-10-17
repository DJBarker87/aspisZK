# Current host C2 embedding primitive and isolated construction core

The actual host `WideExact::from_qm31`, its `canonical_qm31` implementation,
and `WideExact::c0` now have checked extracted bodies. Every raw QM31 limb is
reduced modulo `2147483647`; the lower coordinate contains those four reduced
limbs and the upper coordinate is the actual `QM31::ZERO`. Projection returns
that exact canonicalized QM31. The result does not silently identify arbitrary
raw representatives with their inputs.

`C2HostEmbedding.lean` proves eight primitive lemmas. The generated namespace is
`AspisC2HostEmbedding`; its five functions, five types and two globals are
preserved without naming/body adaptation. One function is the explicitly
synthetic entry wrapper. `source-audit.json` maps all twelve declarations to
exact source or the synthetic wrapper, and re-pins thirty source slices at
`5a28a4b48` (full ref in JSON). `body-audit.json` records every generated body and
signature hash, six explicitly renamed prior carrier/global equalities, and
the old opaque `fromQm` boundary versus this new body's statement diff. This
new namespace is not silently identified with A/C's earlier carriers or their
`B.fromQm` parameter.

`C2HostEmbeddingConstruction.lean` checks the six generic construction-core
lemmas again in a fresh namespace using only the current primitive/Aeneas
closure. It then binds actual per-element embedding into the conditional
construction model, with two retention lemmas. Variant transport, field checks,
encoders and tree construction remain explicit operations; their outputs are
not inferred from their signatures. These are **conditional model results**,
not actual `Backend::c2` or `Commitment::build` execution theorems. The
`literalMessage` ownership/custody conclusion remains open, as do the supplied
H1/G origin, actual transport and encoder correspondence/lengths, raw-to-exact
interpretation, complete experiment recording, packing, salt paths and
checkpoint authentication.

## Focused evidence

| Target | Exit | Wall seconds | Peak RSS KiB | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `crate::embed_project_entry` — Charon | 0 | 0.401943 | 168080 | 0 | n/a: lowering |
| `AspisC2HostEmbedding` — Aeneas | 0 | 0.403950 | 60544 | 0 | n/a: lowering; all generated declarations audited below |
| `AspisC2HostEmbedding.Types` | 0 | 1.882 | 2626760 | 0 | all declarations audited by primitive proof |
| `AspisC2HostEmbedding.Funs` | 0 | 1.669 | 2633028 | 0 | all declarations audited by primitive proof |
| `C2HostEmbedding` | 0 | 1.676 | 2635076 | 0 | 20 reports: empty or standard three |
| `C2HostEmbeddingConstruction` | 0 | 1.880 | 2648256 | 0 | 8 reports: six `[propext]`, two standard three |

The standard three are `propext`, `Classical.choice`, `Quot.sound`. No new
axioms, `sorryAx`, or failed final target. Each receipt records the exact command,
tool/runtime hashes, target, exit, wall time, RSS, swap, revision, source hash,
limits, aggregate reservation, and axioms log. Lowering was source-base
`deb68369ba3ad7cc6706dc24b6503fac1cbe942b`; Lean receipts use base `6aafe82a8`
with the exact new staged Lean source SHA in each receipt. The new files were
not yet committed at execution; their archived bytes equal the committed ones.
Current source re-pinning is read/hash-only. Every compiler/proof scope used
MemoryHigh6GiB/MemoryMax8GiB/MemorySwapMax0. Lean ran sequentially with atomic
external-process prechecks and a200ms monitor; no external overlap occurred.
No dependency, package, SBF, native replay or runtime harness build was run.

The first Types check used the historical environment and failed at missing
`Aeneas.olean`; it did not check declarations. Current checks instead use the
backend's `lake env` snapshot `19815e88217e42aaf971ba17dddf8e88cb00e1cdbd80f8cb076ec37ee490eb76`.
A primitive-proof failure from looping broad `simp` was replaced by direct
`BitVec.toNat_umod` reasoning. A core failure from missing `Aeneas.Std` namespace
was corrected. All failed source/runner/log/receipt inputs remain in the
archive, including the rejected failure's `sorryAx` diagnostics; they are not
counted as proof results.

`primitive-dependency-audit.json` restricts C's current external snapshot to the
3937 transitive Aeneas imports and verifies actual selected source/object hashes.
It includes no `FS2`, `AspisFormal`, `AspisV8R19`, `RawCut` or literal-transcript
model modules. The Aeneas root object is
`d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d`.
The workspace's archived `input-manifest.json` still includes four historical
model cache entries as unused workspace metadata; they are not part of the
new runner's import environment or its audited Aeneas closure. The old13 model
results are separately downgraded in `../c2-historical-context-20261017/`.

`embedding-checkpoint.tar.gz` contains85 hashed members, including original
LLBC, raw Lean generation, source snapshots, all attempts, four final objects,
environments and current dependency snapshot. SHA256:
`ca8095e32c8a8e4f82f2378b8ad6d04d5d1d6cdbd92ed8f5b36b23f173ad41b3`.
`check-embedding.py` validates the packet without executing Lean or a build.
The source/body auditors support deterministic `--check`; the extractor kit's
`prepare-embedding.py --check --out .../input-embedding` validates its input.
