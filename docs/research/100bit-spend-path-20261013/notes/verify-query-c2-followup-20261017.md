# Follow-up to lead deb68369b

Integration branch: `codex/r1-lead-followup-20261016`, isolated worktree
`/Users/dominic/ZK/.worktrees/r1-lead-followup-20261016`.
Baseline: `deb68369ba3ad7cc6706dc24b6503fac1cbe942b`, which accepts
`0189f1094`. The candidate production source is the Digest32 version at
`a555c852664c80000942f0c911e16719a5493625`; its two changed production files
are source-identical in this integration branch. The live worktree and modules
were left alone. No SBF build or readonly runtime harness ran.

## Authorized source changes and extractor blockers

Decisions1d and1e were applied exactly: move the verifier tail into
`verify_finish`, and unroll the eight query digest pairs. The independent
forward/reverse patch audit restores the lead source exactly.

Standing Decision1f then covered these changes, in order:

1. The query trace enumeration fixed point blocked extraction. Expand the
   fixed22 trace statements in the same order; preserve the decoder-returned
   state, errors and trace values.
2. The semantic-round loop fixed point blocked extraction. Expand its ten
   iterations in row order15–24.
3. Borrow translation required moving the unchanged row14 initializer and
   ten-round sequence into private owned-argument helpers. The cfg-specific
   tuple returns carry the same running value, alpha, transcript and prover
   round-check vector.
4. Move the complete unchanged `let boundary = ...` and `let value = ...`
   statements into private helpers. No arithmetic rewrite was made. Their
   implementations remain explicit boundaries in the reachability model.
5. Whole-phase generated printing saturated indentation. Move the unchanged
   single iteration into a private owned helper and call it ten times. The
   first cfg-on-assignment spelling failed Rust parsing and is retained as a
   rejected attempt; the final cfg-exclusive helpers use direct tuple
   assignments. Both helper bodies reverse exactly to the predecessor.

Every source step, blocker and patch is retained under
`tools/callers-current-extraction-kit/standing1f-*`. The independent audit is
`evidence/verify-query-followup-integration-20261017/exact-refactor-reverse-audit.json`.
It checks both cfg alternatives, exact moved statement bytes, all fixed loop
positions, state carry, and the unchanged lead files. No new inline/cold
attributes, public signatures, hash/sampler operations or arithmetic changes
were introduced.

## Native gates on the final source

All targets exited0 with process swap0 and cgroup swap0 under
MemoryHigh=6GiB, MemoryMax=8GiB, MemorySwapMax=0. Native #print axioms is N/A.
Full commands, revisions, source manifests, admission reservations and raw logs
are retained in the linked evidence directories.

| Target | Result | Wall seconds | Peak RSS KiB |
|---|---|---:|---:|
| codec1233-final | all1233 outputs byte-identical | 68.480971 | 540900 |
| saved-proof-counter-final | ordered583 calls identical,349/234 | 114.957637 | 541300 |
| checkpoint23-final | same23 tests pass | 45.790352 | 472296 |
| verify-real-s2-default |112 comparison cases,55 fault points, both observers|4.767929|248192|
| verify-real-s2-detail |112 comparison cases,55 fault points, both observers|3.796710|246860|
| query-migration-102 |102 comparison cases,16 digest positions and decoder|5.044606|261744|

Clean gates: `evidence/final-a555-clean-native-20261017` (archive
`c4acd85d649d75630260a1915ef43c9ec524dcb240bcb2ced45ae5180ab20c0e`).
Injection gates: `evidence/verify-query-native-20261017` (archive
`5c192d1d15fea5207c1f8bb386708b68654ae121dca00eef85792731c2821427`).
Both independent read/hash checkers pass without executing builds.

Verify faults cover Prefix parse, public_transcript, begin, the moved row14
initializer and every lookup/decode/boundary/semantic failure in rows15–24.
The saved S2 proof uses real production arithmetic and transcript operations.
Query tests use saved S2 and synthetic S1/two-fold contexts; the latter are
not asserted to be valid proofs. Digest32 failures use caught aborts because
the trait is infallible. Errors, returned values, state, trace marks and
observer phases are compared in full. The query run at5a28 is re-pinned by
byte equality of transcript.rs and530 other production files; only
r1_semantic.rs changed afterwards. Superseded5a28 verify runs remain historical.

## Current compiled proof results

`evidence/semantic-rounds-current-20261017` retains81 exact source cuts, valid
LLBC, the generated definitions and the bound compact model. The focused
model target exited0 in2.572s at2660300KiB RSS; the ordered-ten-row theorem
exited0 in5.462s at2700816KiB RSS. Both had swap0; all six #print axioms
reports contain standard axioms only. Actual helper success supplies rows15–24,
the exact returned alpha order, unchanged hash, and transcript state carry.
It does not assume arithmetic success or individual child-call success.
Decoder/fold implementations are explicit ordinary function boundaries.

Actual full verify_finish emission is also retained and valid. Emission alone
is not counted as a compiled theorem; its bound caller composition is tracked
separately.

`evidence/source-full25-frames-20261017` and
`evidence/verify-helper-prefix-fe80-20261017` retain the checked source-frame
construction and actual first→tx1→verification-prefix helper reachability.
The full25 finish composition and the selected hread/htyped/ha obligations are
still in progress; see `notes/full25-hread-dependency-map-20261016.md`.

## C2 proof frontier

The earlier nine owned-host and four recorded-experiment model results are
**HISTORICAL_CONTEXT_ONLY**, excluded from the current release count. Their
import paths selected incompatible historical FS2/Uniform objects. The
classification audit retains three exact witness paths and selected source and
object hashes under `evidence/c2-historical-context-20261017`; original archives
were not overwritten.

`evidence/c2-host-embedding-20261017` supplies a fresh four-target proof cone
over current Aeneas/backend imports only. Eight primitive lemmas prove the
actual canonicalized QM31 embedding and retained c0 projection. Six generic
construction-core lemmas and two binding lemmas were freshly checked in that
same environment. All28 axioms reports are standard-only, all targets exit0
with swap0, and the3937-module source/object closure is hash-audited. The
actual embedding is canonicalized limb-by-limb modulo P; no raw-limb identity
is substituted for it.

These results do not yet prove actual Backend/build execution constructs the
owned vectors or literalMessage. Packing, variant/encoder transport and exact
length/content, salt/path, custody, and checkpoint remain separate obligations.
Hashes and samplers are not substitutes for the full C2 witness.

The remaining compiler frontier is isolated in
`evidence/c2-helper-root-diagnostics-20261017` (archive
`9b64fe50df2f41656258a777ce5144a91a2c8858755587f6cc82fbc3b63b93b0`).
Rooting the actual copy helper alone still fails Aeneas at
`SymbolicToPureAbs.ml:1313`; rooting only the unchanged encode/retain prefix
fails at `InterpAbs.ml:191`. Both have valid error-free LLBC but no accepted
Lean emission or theorem. Their Charons exit0 and their Aeneas runs exit2,
with swap0 and the same6/8GiB caps. The retained102-member archive and
deterministic input generators pass the read/hash-only checker. No viable
production-source refactor was demonstrated or adopted. The six exact source
spans and preservation conditions are recorded in
`evidence/c2-host-embedding-20261017/next-source-bridge-plan.json`.

## Outstanding work

Actual finish→full25 byte identity, generic selected hread in a coherent current
closure, and source/address/table/typed-context identifications remain distinct.
The latter cannot follow from strict parsing alone. Circle25/26, row26 reseed,
query returned-state carry and the opening schedule are staged for focused
checks; no all33 completion claim is made here yet. Declaration re-pinning is
being extended to the newly accepted cones before the final checkpoint.
