# Checkpoint and global log: stage-1 result (2026-10-20)

Partial result at base `74f689738905518e54f8532eaf368e333cefbf16`, branch
`codex/cx-ckpt-log-20261020`. R15 is blocked by a missing accepted writer
extraction. R10 has a checked conditional log assembly and rows 0–24 bridge;
whole-tx1 call coverage is still an obligation. Neither row is closed.

Paths below are relative to this research directory unless rooted at `programs/`
or `crates/` (repository root). No existing Lean module or production source
was changed. No stage-2 extraction, runtime test, full release replay, or
artifact re-pin was performed.

## R15: the requested writer is not in the pinned extraction

`lean/bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean:15` declares
`Tx1Model.Boundaries.finish` as a function parameter returning arbitrary
`Result (Result (Vec U8) verifier.Error)`. The tx1 body calls it at line 147;
there is no emitted checkpoint serializer or account-write body in this model.
Its accumulator argument is the newly allocated accumulator, not the
post-query accumulator; query execution is also inside the finish boundary.
`design/J1-PREPARED-TX1-REPIN-ADDENDUM-20261016.md:12` explicitly calls
`tx1_finish` signature-only, and excludes the diagnostic tail emission at
line 8. The kit's `tools/tx1-caller-extraction-kit/input-accumulator/lib.rs:929`
has `checkpoint(...){unreachable!()}`; its source-pins.json:869 expressly
forbids assigning semantics to boundary stubs.

The countermodel to a claim based on this signature alone is compiled in
`lean/RawTx1CheckpointBoundary.lean:12`: `withOutput B x` replaces only
`finish` with successful constant output x. `arbitrary_finish_output` (line 16)
and `distinct_finish_outputs` (line 27) prove that identical arguments admit
arbitrary, distinct outputs across these boundary instantiations. For example,
choose the empty vector and a one-byte vector. Thus neither a checkpoint
length nor digest fields follow from the accepted boundary signature. This
is an extraction obstruction, not a counterexample to the Rust writer.
Per the task's stop rule, R15's requested source proof stops here.

The actual Rust targets, checked by source inspection (not Lean proofs), are:

- `crates/aspis-r1-cost-probe/src/verifier.rs:271–285`: writer takes
  **Prepared, Accumulator, proof, public, hash**. Bytes 16–47 are
  `hash.digest(&[proof])`; bytes 48–79 are `hash.digest(&[public])`.
  These are two separate digests, not a hash of the concatenated buffers.
  The final 32 bytes hash `"UNPROVED:R1:checkpoint" || preceding bytes`.
  The other serialized data include all Prepared fields and accumulator data.
  Dependency on Prepared cannot simply be dropped: changing `p.state` while
  keeping the other writer inputs fixed changes bytes 80–111. A determinism
  statement in terms of proof/public/post-accumulator must fix the oracle and
  derive Prepared from the successful preparation, not quantify over arbitrary
  Prepared values. No claim is made that both changed states are reachable.
- `crates/aspis-r1-cost-probe/src/candidate.rs:192–214`: the adopted tx1
  calls `checkpoint(&p,&a,proof,public_bytes,hash)` **after** the compact
  multiproof checks, query loop and pending-weight finish. Thus the hashed
  proof is the stored compact buffer, not the expanded semantic scratch.
  `verifier.rs:396–401` selects this entrypoint and fixes proof length 57,607
  and split 10. The historical accepted Tx1Model is not this body.
- `programs/r1-cost-probe/src/r1_pool_adapter.rs:210–222` checks exact
  `checkpoint_size(S2)`, verifier ownership and privileges. Stage1 checks
  distinct accounts at line 953, checks every checkpoint byte is zero at
  lines 958–960, passes the compact proof slice and original public bytes at
  line 981, then requires equal output/account lengths and copies at
  lines 982–985. Those account predicates are outside the retained tx1 model.
  `programs/r1-cost-probe/src/lib.rs:55–63` is the G_R1.7 admission gate;
  lines 73–77 give the analogous non-adapter legacy writer checks.

Remaining named obligations (not axioms or proved source results):

1. **R15.Tx1WriterExtraction**: accepted emitted bodies for the adopted
   tx1 query/checkpoint tail and checkpoint serializer, connected to the
   frozen candidate entrypoint. Prove the two digest slices above, checksum,
   exact size, and dependence on the actual derived Prepared/post-query state.
2. **R15.Tx1AccountWrite**: extract the adapter's guard/write path and derive
   all-zero, exact-size, ownership, distinctness and sole-write predicates
   from successful execution (G_R1.7/G_R1.9).
3. **R15.Tx2ResumeFields**: from successful resume on tx1's checkpoint and
   identical proof/public bytes, recover the serialized Prepared and
   accumulator fields (state, roots, gamma/kappa/alphas/rho, queries,
   semantic_alpha, z, claim, next, rhs, power, weights), with canonicality,
   allocation-success and range premises derived from reachable tx1 states.
   The source reader is `verifier.rs:294–311`. This is not a universal
   round-trip for arbitrary malformed Prepared/Accumulator values.
4. **R15.Tx2SameBuffers**: digest comparisons at `verifier.rs:297`, byte
   identity under the separately charged collision event, and runtime
   checkpoint provenance/ownership across transactions. Waits on stage 2.

## R10: checked conditional composition

`lean/RawTx1DigestLog.lean:14` defines actual call witnesses against the
extracted `Digest32.digest` API (parts are slices of slices of U8; outputs
are Bytes32, decoded into the existing byte-oracle State). Its named
`ByteOracleBackend` (line 20) states that successful calls agree with one
Hbytes after flattening the parts. This ROM/backend interface is explicit:
arbitrary Digest32 implementations need not be independent of segmentation
or backend value, so this cannot follow from the trait signature.

`log` (line 27) retains the actual initializer, the three calls per source
row from `SourceDigestLog`, supplied sampler suffix calls, and supplied
remaining tx1 calls. `prefix_contained`, `log_actual`, `log_consistent` and
`same_address_same_output` prove containment, successful-call witnesses,
one-oracle consistency and repeated-address agreement. Suffix/rest witness
premises remain explicit. The initializer plus 25 rows contribute 76 calls;
this is not the total tx1 call count.

`every_reached_call` (line 96) proves the conditional tx1 embedding under
**Tx1InventoryComplete** (line 37). This completeness premise remains
undischarged: the retained extraction does not expose the complete query,
Merkle, checkpoint or adapter call traces. In particular, selecting empty
suffix/rest lists does not prove all tx1 calls are represented. The assembled
list is an inventory log; interleaving/order and first-read accounting need
an execution trace and are not asserted.

`lean/RawTx1GlobalOracleFull25.lean:16` applies
`SourceGlobalOracleFull25.full25_initial_and_positive_prefix`
(`lean/RawSourceGlobalOracleFull25.lean:33`), discharging its two global-log
premises (lines 48–49) from the assembled log. The exact row-zero, literal
prefix and final-state conclusions are retained. Parsing, trace reachability,
row order, decoding, frame bounds and public/root carrier equalities are
still the original premises. `lean/RawSourceLiteralFull25Prefix.lean:51`
is the complementary constructed-source-oracle theorem; its source-oracle
construction does not establish a complete global execution log. It is not
silently substituted for Hbytes here.

The sampler job landed during this run: source commit `3d80d38d1`, receipts
`6b1942982`, lead addendum `1d9b0f721`. It is partial and explicitly does not
construct a complete suffix log. `lean/RawTx1SamplerSuffixOracle.lean:16`
converts ByteOracleBackend to the exact functional digest interface consumed
by the landed source bridges. Its opening, circle25 and circle26 theorems
apply those bridges under the SAME Hbytes as the tx1 log. Row 26 retains the
extra P3 reseed; opening rows cover 27–30 and 32. All original call-success,
message/frame, state, tag/length and carrier premises remain. Row 31's
complete eight-block source trace/scan-selected state, suffix call coverage,
concrete scalar/point transport and current-caller re-pins remain open as in
`design/SAMPLER-ROWS-25-32-20261020.md:40–77` at that source commit.

**SamplerRows25To32Logged** (`RawTx1DigestLog.lean:40`) therefore remains a
coverage obligation, rather than being declared solved by local suffix laws.
The external landed module is imported from its retained compiled cache;
`landed-sampler-pins.json` pins its committed source and receipt/object hashes.
No uncommitted worker source was used. This branch depends on the landed
sampler commits for replay; it does not duplicate their modules.

**Tx2EmbeddingObligation** and **CrossTransactionConsistency** are named
Props at `RawTx1DigestLog.lean:45,50`. The latter quantifies over both logs
under the SAME Hbytes; two independent per-transaction oracles do not meet
it. Neither is proved. Ordering, memoized execution law, first-read budget,
adapter/runtime calls, frozen-source re-pins and whole-tx1 inventory coverage
also remain open. Hence this result does not make R1/R2/R11 unconditional.

## Verification and handoff

All four new modules compiled individually with Lean 4.32.0, `-j1 -M4400
-DElab.async=false`, `/usr/bin/time -l`, the shared mkdir lock and private
`/tmp/codex-cx-ckpt-log-20261020-objects`. Twelve theorem axiom audits are
standard-only (one theorem has no axioms). Every attempt had zero swaps.

| Target | Exit | Wall (s) | Peak RSS (bytes) | Final attempt |
|---|---:|---:|---:|---|
| RawTx1DigestLog | 0 | 13.957 | 3,436,363,776 | log-v1 |
| RawTx1CheckpointBoundary | 0 | 5.821 | 2,245,033,984 | checkpoint-boundary-v1 |
| RawTx1GlobalOracleFull25 | 0 | 23.618 | 3,431,809,024 | full25-cache-v6 |
| RawTx1SamplerSuffixOracle | 0 | 16.838 | 3,415,556,096 | suffix-v1 |

`evidence/checkpoint-log-tx1-20261020/manifest.json` contains every command,
source/base revision and SHA, dependency fingerprint, exit, timing, RSS,
swap count, full axiom output and failed-attempt diagnostics. Five full25
import failures are retained: missing initializer dependency, missing typed
full-prefix dependency, partial namespace shadowing, and two paths missing
the codec dependency. Each successor changes the cache search path;
`full25-cache-v6` restores the exact codec object SHA from the accepted
packet. No memory failure or cap increase occurred. No unchanged passing
Lean target was rerun. No shared compiled object was overwritten.

`python3 evidence/checkpoint-log-tx1-20261020/packet.py` verifies the packet
without running Lean. No binaries/objects are committed. Replaying this
branch requires the already-landed sampler source commit `3d80d38d1` (its
receipt commit is `6b1942982`). The source freeze and S1–S10 re-pin obligations
continue to apply; these historical extraction bridges are not a theorem
about a newly re-extracted compact verifier. Next work is accepted tx1 tail/
writer/account extraction and an actual complete call inventory, followed
by the separately assigned stage-2/cross-transaction work.
