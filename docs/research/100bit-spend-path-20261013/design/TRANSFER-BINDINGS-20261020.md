# Transfer statement bindings and cross-stage obligations (2026-10-20)

R8 is proved for the retained adapter extraction. R9 has typed, named obligations
and a conditional composition; transaction-level discharge remains open.
All paths below are relative to this research directory unless prefixed otherwise.

## R8: exact transfer arm

`lean/ExtractedAdapterTransferBindings.lean:206`
(`AspisR1AdapterReconstruct.TransferBindings.reconstruct_transfer_bindings`)
mirrors the withdrawal theorem. Given only `request.public = PrivateTransfer p`
and `reconstruct_asq8_statement request a candidate = ok (.Ok out)`, it proves:

- checked increment of the live pair index to the candidate index;
- master asset equals `p.asset_id`;
- the three structural account keys are nonzero and the selected lane is below 8;
- pool, deployment domain, live-snapshot pool, checkpoint sequence and historical
  root bind to the fixed account records;
- the actual nullifier-to-output-lane computation returns that selected lane.

The validator-prefix lemma is at `lean/ExtractedAdapterTransferBindings.lean:88`.
It inverts the actual validator only as far as the lane guard, preserving the
remaining late/tree computation as part of the success premise. Array equality
uses the backend's symbolic slice-comparison theorem, without enumerating arrays.

`reconstruct_transfer_payload` at line 286 additionally proves the entire output
is `PrivateTransfer (common a candidate) p`, the ordered output commitments are
exactly `(p.recipient_commitment, p.change_commitment)`, and the nested 216-byte
payment encoder succeeds on this same `p`. Its encoder-prefix lemma is at line
238. These commitments are public note commitments, not a proof of note openings,
spend relation, or custody. The actual transfer record has eight fields and no
destination token account (`lean/extracted-adapter-reconstruct-20261016/
AspisR1AdapterReconstruct/Types.lean:215`; current Rust
`crates/aspis-statement/src/pool_v1/payment_relation.rs:46`).

The actual Rust functions are `programs/r1-cost-probe/src/r1_pool_adapter.rs:830`
(transfer box) and `:857` (reconstruction); the copied common fields are at `:810`.
The current validator is `crates/aspis-statement/src/pool_v1/
pair_forest_terminal.rs:241`. The downstream output-note relation is a separate
semantic obligation; the adapter copies the payload rather than computing note
commitments from secret witnesses.

## Extraction and current-source comparison

No new extraction was needed: `AspisR1AdapterReconstruct` already contains both
arms. Its original extraction is pinned to Rust `42e5ca2011c39ee9770afc798282ff861b092428`
in `tools/adapter-reconstruct-extraction-kit/source-pins.json`; the received
Charon/Aeneas scope/tool/resource receipts are in
`evidence/adapter-reconstruct-432-20261016/manifest.json`. The generated Funs
SHA-256 is `bce4345d53e4bf18e05f475b65521324c0b0fbcb24dcb182ac9df64da922d0f2`.
The existing checked type-name overlay (`lean/bridge-adapter-public-20261016/`)
renames only the payment-error discriminant instance. It is reused unchanged.

`evidence/transfer-bindings-20261020/source-comparison.json` compares all five
adapter declarations byte for byte to this worktree's base `f2c084bc8` and hashes
all eleven project Rust files labelled by the generated Types/Funs. All five
adapter declarations are unchanged. Changed dependency files add the semantic
selector or change decoders outside this reconstruction/encoder cone; their
full diff is retained in `dependency-diff.patch`. The terminal validator, payment
encoders, account lane function, late encoder, and relevant type definitions
are unchanged. `compare_sources.py` reproduces the hashes and diff. The original
cut generator's `--check` passes. This is source inspection and pin evidence,
not a theorem of Rust/compiler/runtime preservation. The adopted binary
multiproof changes no function in this adapter cone; this proof neither models
nor changes root absorption or multiproof verification.

## R9: named obligations against existing definitions

The new module `lean/ExtractedAdapterStageBindingObligations.lean` fixes a
field-by-field adapter-to-serializer map for both variants (`toSerializer`, line
57). It copies all public fields and all nine snapshot/candidate fields. Its
selector agrees by inspection with the current Rust `semantic_public` method
(`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:120`); an actual
execution/refinement link is not claimed.

| Obligation | Exact definition in the new module | What remains to establish |
|---|---|---|
| `SerializerWitness stage1 bytes` (`hs`) | line 63: actual extracted `Public.public_bytes stage1 = ok (.Ok bytes)` | Accepted stage-1 execution reaches this exact public argument and succeeds |
| `SuppliedPublicBinding stage1 supplied` (`hbind`) | line 67: fixed `toWire (projectRaw stage1)`, mapped by `SemanticPublicWire.toPublic`, equals `some supplied` | Equality to the actual verifier's supplied public |
| `PaymentGuard stage1` | line 73: existing `PublicRawAmountGuard.PaymentAmountGuard (RawBridge431.project stage1)` | Trivial for transfers; withdrawal amount validation must be linked |
| `SameSemanticPublic stage1 out` | line 78: `stage1 = toSerializer out` | Actual stage-1 argument versus stage-2 reconstruction, including checkpoint/candidate provenance |
| `Stage2SameBytes request a candidate bytes` | line 84: there exists actual successful reconstruction `out` whose fixed semantic serializer returns the very same `bytes` | Derived conditionally below; not an assertion that stage 2 calls the serializer |

The `hbind` form is compatible with the existing `wire`, `hw` and
`supplied = toPublic wire` hypotheses: `hbind_of_wire` proves it (line 94).
`serializer_supplied_public` (line 118) proves the actual `parsePublic` equation
from `hs`, the payment guard, and `hbind`, using the existing serializer
refinement and codec theorem. `transfer_payment_guard` (line 90) discharges the
guard for transfer. `same_public_unique_bytes` (line 135) proves determinism on
the same fixed argument. `r9_of_same_public` (line 147) composes these short
facts with actual reconstruction success and the named equality obligation:
it proves `Stage2SameBytes` and parsing to the supplied public, for both variants.
`reconstruct_transfer_projection` (line 165) derives the fixed transfer projection
from R8 without assuming another payload equality.

These are conditional theorems, not a completed R9. Current stage 1 decodes ASF8
and selects the semantic argument in `programs/r1-cost-probe/src/lib.rs:42`;
the helper invokes `public.public_bytes()` in
`crates/aspis-r1-cost-probe/src/r1_semantic.rs:67`. Its successful-helper inversion
already exists in `lean/ExtractedPublicPreparationSuccess.lean:35`; composing
that helper's reachability from the accepted transaction is still owed. The
current serializer body is
`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017`.
Stage 1 of the adapter uses the semantic argument at
`programs/r1-cost-probe/src/r1_pool_adapter.rs:981`. ASQ8 reconstructs at
`:915` and calls `tx2_authenticated` at `:1020`; the separate resume
checkpoint/public checks start at `crates/aspis-r1-cost-probe/src/verifier.rs:294`.

Semantic serialization omits account keys, pool/domain, anchor sequence, and
other metadata (`lean/PublicExtractedRawBridge431.lean:28` and `:40`). Therefore
no semantic-byte injectivity argument is used to recover these fields. R8 binds
them structurally; authentication, admission, saved checkpoint, proof-buffer
candidate provenance and cross-transaction linkage remain separate obligations.

## Focused verification and boundaries

All checks use Lean 4.32.0, `-j1 -M4400 -DElab.async=false`, the shared mkdir lock,
`/usr/bin/time -l`, and a private `/tmp/codex-cx-bindings-20261020-objects` tree.
No existing module under `lean/` was edited and no shared object was rewritten.
Only the four small adapter prerequisites and the new modules are checked;
backend, mathlib and serializer dependencies are reused, with import-object
hashes recorded. There is no full manifest, SBF or Rust regression replay.

Retained diagnostics: an initial R9 import attempt was missing a cache member;
completing the search path exposed the adapter/decoder generated-instance name
collision. That attempt was replaced by direct serializer obligations, avoiding
the decoder import. A subsequent check found the cached codec object lacked the
later `parsePublic_of_decode` export. The final source proves its short
wire-specific consequence from the retained encode-to-wire law and the actual
wire round-trip theorem. The intermediate failed check prints `sorryAx` as
Lean's error recovery; it is not an accepted theorem or a source placeholder.
No target was killed for memory and no memory cap was raised.

The final checks passed: R8 in 6.159 s (peak RSS 2,235,957,248 bytes), R9 in
10.756 s (peak RSS 3,268,804,608 bytes), both exit 0 and zero swaps. There are
19 standard-only axiom reports for the two new modules, including every private
proof; with the reused adapter prerequisites, 25 reports across six checks.
The four failed R9 attempts and their errors remain in the packet; a queued
symbol-inventory diagnostic was cancelled before Lean started and made no
proof claim. `manifest.json` uses `focused-extractor-proof-packet-v1` and records
module/source/import/object hashes, base source revision, command, exit, wall,
RSS, swaps and complete axiom lines. `packet.py` independently verifies the
receipts and current source hashes without recompiling. No binaries are added.

R8 is therefore ready for lead review at the same retained-extraction scope as
R7. R9 remains open at the transaction/caller/checkpoint boundary. Nothing in
this packet establishes owner/PDA authentication, live account provenance,
custody, the source-to-runtime refinement, or end-to-end soundness.
