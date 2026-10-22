# Prover commitment continuation 43

Target not yet established. Worktree base: 5296bb1e509fdd32ec3cbb4fc70f640db071e7c7.
Branch: codex/cx-prover-commit43-20261022. No shipped sources changed.

## Stage 1: sixteen-candidate owner

The per-candidate native transition gate passes all 174 checks for arbitrary
64-byte draws, OS status, public nonce, retained bytes and every reachable
call/draw counter in the 0–15 candidate prefix. The extracted native body is
verbatim except for explicit stop/continue outcome wrapping: success and OS
error become terminal `Some` values; fall-through becomes `None`. The prior
verified zero-helper contract is reused as a verified substitution, not a
new trust item. No whole-loop harness runs. The Kani gate verifies bounded
native execution; its source mapping remains an external P6 boundary, not a
Lean proof about Rust syntax.

`ProverCommitNative43.range_run` proves the native `Range<usize>` denotation
by induction over the remaining candidates, preserving the complete
schedule/tape/state transition. `increment` proves no counter wrap before 16.
`generate_owner` identifies the zero-nonce guard and sixteen-step loop with
`AspisR1PublicNonce41.owner.generate`; `continuation` retains arbitrary
subsequent observations of both result and state. This closes the specific
part-42 native candidate/finite-loop verification gap, with the native
boundary and its independently proved Lean composition kept explicit.

J9494 is a rejected elaboration draft. J9495 accepts all five new theorems:
exit 0, wall 2.19 s, peak RSS 4,173,992 KiB, zero swaps, each axiom list
[propext, Classical.choice, Quot.sound]. Exact targets, source hashes,
dependency fingerprints, commands, source revision and full compiler output
are in `../../100bit-spend-path-20261013/evidence/prover-commit43-20261022/lean/`.
The native receipt and pinned inputs are beside them under `native/`,
`native-input-snapshots/`, `pins/` and `harness/native-source-check.json`.
No inherited Lean source/object is changed by the new module.

## Remaining stages

Native simulator publication, the literal source experiment conversion,
`shippedProverExperiment`, both WholeRunJoins and the endpoint without
RustProverRefinement remain open at this stage checkpoint. Trust list remains
P1, P7, TrustedStd, E1, E2. No nonce law or ledger cap is added. D143
observables and D146's announced source-representable statement domain are
retained. No release claim or endpoint premise removal is made here.

## Publication caller checkpoint

J9498 accepts `ProverCommitPublish43`: exact six-part per-query byte order,
finite query-loop composition, node-slot fold/recursive agreement, padded
slot lengths, both final length guards, and replay/transcript/Merkle/merge
error precedence. J9499 accepts `ProverCommitLeaves43`: every pair consumes
two successive salts from the same retained coin state, folded leaves consume
one, all writes transport through the existing TrustedStd insert-state law,
and ordered iteration transports unchanged. J9503 accepts
`ProverCommitCompact43`: exact zero-high-half acceptance and low-half bytes,
compact-value fold/recursion, semantic-row fold/recursion, and successful
compact length. These are **local caller/algebra theorems**, not yet a
complete source publication certificate. Codecs and multiproof calls remain
explicit results in the publication driver; their concrete source identities
are not silently assumed. No new TrustedStd field or caller law is added.

J9496–9497 and J9501–9502 are rejected elaboration drafts. J9500 was refused
because a receipt from another job already exists; no compiler ran and that
receipt is not attributed here. A read-only inventory selected the next free
assigned numbers. Accepted wall/RSS/swap fields: J9498 1.38 s / 2,542,888 KiB /
0; J9499 1.33 s / 2,535,676 KiB / 0; J9503 1.51 s / 2,532,328 KiB / 0. All
exit 0; every printed axiom list is a subset of the three standard axioms.

The native leaf/query transition passes with arbitrary 4-byte payloads,
ordered coin-call trace and all returned salts, and length plus an arbitrary
selected output byte (48.626 s, 2,761,680 KiB, zero swaps). The initial full
output comparison failed an unwinding assertion because its 108-byte buffer
exceeded the fixed comparison unwind bound; it is rejected, not treated as
a source counterexample. The replacement changes the observed comparison,
not the source body or the unwinding-assertion policy. The compact-cell
transition passes 578 checks on all 32 bytes (including high-half rejection),
with native source equality audited modulo whitespace and visibility only.

The native merge call-boundary transition passes on arbitrary old/new 32-byte
answers, arbitrary address and retained frame, under the already named
TrustedStd insert contract. This checks caller control, not BTreeMap internals.
The full map state/ordered merge transport is the existing universal
`ProverCommitMerge33.native_ordered_loop_decode`. The separate larger sorted
substitute gate remains pending and is not used as accepted evidence.

The initial entropy gate collapsed OS error payloads to a status. The stronger
`candidate-full-bytes-error-payload-v2` additionally checks preservation of an
arbitrary opaque error code (u32 carrier), with exit 0, wall 3.044 s, RSS
277,032 KiB, zero swaps. The extracted owner and Lean induction already
preserve their generic error payload. The stronger native gate is the
accepted final boundary; the status-only gate is retained for provenance.
