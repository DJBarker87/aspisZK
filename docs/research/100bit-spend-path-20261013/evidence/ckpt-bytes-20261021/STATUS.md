# Checkpoint byte and decoder continuation

Branch codex/cx-ckpt-bytes-20261021. New Lean modules only; no shipped,
protected, sibling, root checkout or shared object edits. Local compiler,
private object directory, shared mkdir lock, -j1 -M4400 -DElab.async=false.
Each attempt has exact command, source/import hashes, source revision, exit,
wall, peak RSS, swap and complete axiom output in manifest.json. Failed
compiler recovery reports are excluded from accepted evidence.

## Stage 0: statement and scalar inspection

Read CONES-P6 item 3 and ckpt-abi2..5 STATUS. Reuse the inherited exact K
writer and C5 word/field codecs within their recorded domains. The scalar
inspection module prints the actual imported operations and elaborated
extracted calls; it asserts no source refinement. No Rust/Kani/host or ELF
build is needed for this inspection. The local rules override the old
common-rule host-only Lean paragraph; no env J attempt is consumed.

Two statement boundaries are under focused kernel verification:
- e_byte at index 32 performs an out-of-bounds limb read, so unconditional
  all-index success is false. In-range totality is the intended byte law.
- decode_k_spec has no length guard, reads only offsets 0,4,8,12, and can
  accept a trailing byte. Exactly-16 section adoption is necessary for a
  strict canonical K encoding claim. decode_e_spec does check length 32.

Neither boundary disproves a correctly bounded production section theorem.
No complete checkpoint cone, decoder join, premise removal or frozen release
result is claimed. Next local target: CheckpointBytesE.e_byte_raw, followed
by exact C5 byte projection and bounded sparse-body composition.

## Stage 1: checked scalar arithmetic

CheckpointBytesArithmetic.{div_four,rem_four,mul_eight} prove actual checked
Usize operation equalities, without fixing pointer width or assuming successful
calls. Division is bounded to i<65536; multiplication takes i<4. These
symbolic arithmetic lemmas replace unfolding the platform-sized BitVec
operations. Final attempt 2: exit 0, 19.93675470817834 seconds, peak RSS
3478847488 bytes, zero swaps, revision 6a952a828 (full SHA in receipt).
All three axiom reports are [propext, Classical.choice, Quot.sound].
The failed first attempt used the wrong WP/exists interface for rem/mul and
an insufficient division bound; its recovery reports are not accepted.

## Stage 2: kernel-checked target obstructions

CheckpointBytesBoundaries.e_byte_out_of_range proves e_byte q 32 returns
fail arrayOutOfBounds for every raw wide value. k_accepts_trailing_byte
constructs a 17-zero-byte slice accepted by the extracted decode_k_spec.
Thus unconditional e_byte success and unbounded standalone strict-K
accept-exactly-16-byte-encoding statements are false. This stops those
unrestricted formulations under common rule 4. It does not invalidate
in-range totality or exact-width production Reader.k adoption.

Final boundary attempt 4: exit 0, wall 12.324110167101026 s, peak RSS
3668000768 bytes, zero swaps, revision 11b1d46c2 (full revision and pins in
receipt). Both axiom reports are [propext, Classical.choice, Quot.sound].
Failures 1..3 preserve the platform-width and Array.make elaboration issues;
no limit increase or unchanged retry occurred. The final proof uses the
symbolic division lemma and only a tiny 17-byte counterexample.

Independent source composition constraint: verifier.rs resume lines 428..431
can return Error::Allocation from heap::filled before readWeights/Box::new.
The imported ResumeOps exposes filled as a fallible operation, and inherited
std Vec content erases physical capacity. An all-canonical-input production
success iff needs allocation availability or a success-conditioned claim;
neither follows merely from caller binding or field provenance. This is a
source/model boundary, not a cryptographic assumption or an allocator failure
measurement. No additional premise is silently inserted into P6.

## Stage 3: complete extracted E-byte execution and C5 byte meaning

CheckpointBytesE.e_byte_raw proves in-range success for every raw WideExact,
with no canonicality or supplied-success premise. It composes checked scalar
arithmetic and eight symbolic 32-bit words; its finite case split has only
32 scalar positions. CheckpointBytesETotal.e_byte_all covers every Usize:
inside 0..31 it returns the exact raw byte, otherwise arrayOutOfBounds.
CheckpointBytesEC5.rawBytes_c5 and e_byte_c5 identify those bytes with C5's
encodeE on CanonicalWide values. Canonicality is necessary only for the
raw-word/exact-field quotient bridge. No full body/checkpoint is reduced.

| Target | Attempt | Exit | Wall s | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|---:|
| CheckpointBytesE | 10 | 0 | 16.32794408267364 | 3813359616 | 0 |
| CheckpointBytesEC5 | 1 | 0 | 5.133784458041191 | 3656663040 | 0 |
| CheckpointBytesETotal | 1 | 0 | 15.043641124852002 | 3651796992 | 0 |

All six final theorem axiom reports are [propext, Classical.choice,
Quot.sound]. Revisions are f98510f8e (exact full SHA in receipts). Attempts
1..7 and 9 retain elaboration/simplifier failures. Attempt 8 exits 0 but is
REJECTED: this toolchain's bv_decide emits native axioms. It is explicitly
non-current and not accepted evidence. The replacement normalizes only
symbolic word shifts, byte truncations and tiny powers, using ushiftRight_eq
before the Nat projection lemmas and omega. The launcher now enforces the
standard-axiom whitelist in addition to exit/source checks. No bv_decide
remains in the accepted source, and no native generated axiom is imported
by the current E object. No memory/heartbeat/recursion cap was raised.

Exact next byte consumer: a new sparse body_byte/C5 theorem over canonical
Prepared/Accumulator fields, saved.next=10, bounded queries and 64 weights.

## Stage 4: sparse-body arithmetic and explicit allocation boundary

CheckpointBytesBodyArithmetic proves exact checked subtraction, division and
remainder for the bounded sparse-index domain. Final attempt 2 exits 0,
5.958834458142519 s, peak RSS 3648323584 bytes, zero swaps, revision
0e57b8b1d. Its three axiom reports are standard. Attempt 1's subtraction
postcondition/bound errors are retained and excluded.

CheckpointBytesAllocationBoundary proves reservation rejection and the
absence of an all-reservation-state successful roundtrip for the inherited
fallible allocatedOverwrite model. Attempt 1 exits 0, 14.55853445827961 s,
peak RSS 3631251456 bytes, zero swaps, revision 0e57b8b1d. Both reports are
standard. This is a model-step impossibility, not a physical allocator
counterexample or a refutation of success-conditioned source refinement.
It records why allocation success cannot be inferred from canonical bytes.
The exact source files/model boundary are pinned in source-pins.json.

NEXT.md states the separate S2S10CallerBinding and S1S7S8StateProvenance
interfaces and identifies reached_stage/strictStage as the retained consumer.
Neither premise is hidden in P6, and no unproved source equality is assumed.

## Stage 5: all 18 raw-field reference blocks and checksum equal C5

CheckpointBytesBlocks.{blocks_c5,body_c5,encode_c5} prove complete fixed-block
composition from a raw scalar field inventory, including all 64 weights,
queries, header next=10, proof/public hashes and checksum over the complete
body. rawK_c5 reuses the actual nested source K writer; rawKs_c5 inducts over
symbolic vector length. E fields use the newly proved rawBytes_c5. No
per-block byte equality or checksum equality is supplied as a premise.
CanonicalFields spells out every raw four/eight-limb canonicality bound;
Prepared and accumulator interpretations are concrete definitions.

This closes the **raw-field reference block composition**. Fields is an
explicit reference carrier. Identifying it with the extracted Prepared /
Accumulator sparse body_byte and adopting the actual production writer
remain separate; this theorem does not silently count that as done.

Final CheckpointBytesBlocks attempt 2: exit 0, 12.403295292053372 s,
peak RSS 3655057408 bytes, zero swaps, revision 0e57b8b1d (full SHA and
object/source/import pins in receipt). All five reports are standard.
Attempt 1's dependent-proof map/ofFn rewrite failed; induction replaces it.
No full byte buffer or long vector is evaluated, and no cap is raised.

## Stage 6: six extracted sparse wide intervals

CheckpointBytesSparseE proves the source dispatch and exact C5 bytes for
all six wide-field intervals: gamma at 176, kappa at 208, alpha0 at 240,
alpha1 at 272, claim at 632 and RHS at 664. Every byte index inside each
32-byte interval is symbolic. Each C5 theorem requires only that particular
raw field's canonicality; dispatch itself needs no canonicality or supplied
source-call success. No header/whole-writer equality is assumed.

generate_sparse.py --check validates the named intervals against the actual
extracted threshold schedule. It emits six separate symbolic theorem
applications/branch proofs, never concrete checkpoint reduction. The prior
aggregate declaration timed out at the default heartbeat limit (attempts
2..4). The replacement isolates one interval, proves its guards explicitly,
then composes the named E theorem; no cap is raised. Attempt 1's reserved
binder, attempt 5's redundant trailing tactic and attempt 6's missing
normalized division rewrite are retained as failed evidence.

Final attempt 7: exit 0, wall 35.868560292292386 s, peak RSS 3536617472
bytes, zero swaps, revision 0a83ad804. All twelve axiom reports are standard.
This closes six sparse intervals, not all body bytes. K sections, literal/
digest/query byte sections and a complete body/C5 aggregate remain separate.

## Stage 7: extracted K selector and every sparse K field interval

CheckpointBytesK.k_byte_c5 composes the full nested emitted encode_k with
the actual extracted k_byte index operation, deriving success and exact C5
bytes for every in-range index on canonical raw words. CheckpointBytesSparseK
adds exact source dispatch and C5 byte laws for rho, power, every semantic
alpha, all four coordinates, and each of 64 weights. The indexed sections
quantify over their ordinal rather than reducing the vector. The weights
require its physical content length=64; the decoder/allocator producer is
not assumed proved. Each C5 theorem names that selected field's canonicality.

generate_sparse_k.py --check validates the generator and source threshold
schedule. No section call-success or body equality premise is supplied.
Final K attempt 2: exit 0, 15.872148500289768 s, RSS 3644260352 bytes, zero
swaps, revision 0a83ad804. Initial K attempt missed the explicit list lookup
rewrite and is retained as failed. SparseK attempt 1: exit 0,
26.897038583643734 s, RSS 3604922368 bytes, zero swaps, revision 7d0b16eea.
All seventeen new axiom reports are standard. Full revisions and resource,
source, object and dependency pins are in the receipts. No cap was raised.

## Stage 8: literal header and five sparse digest/state intervals

CheckpointBytesHeader.header_bytes proves every one of the 16 literal
header bytes when source next.val=10. next_cast supplies the cast law
symbolically. Final attempt 1 exits 0, 18.502187584061176 s, peak RSS
3630186496 bytes, zero swaps, revision 335b96d88. Both axiom reports are
standard. Only these tiny header positions are split, not a whole body.

CheckpointBytesDigest.bytes_stateOf identifies an arbitrary raw 32-byte
array with its exact C5 State interpretation. CheckpointBytesSparseDigest
then proves source dispatch and byte content for proofHash, publicHash,
state, root0 and root1. Its generator checks the extracted threshold
schedule. Digest attempt 2: exit 0, 7.301299958024174 s, peak RSS 3644194816
bytes, zero swaps, revision 7d0b16eea. SparseDigest attempt 1: exit 0,
27.438740625046194 s, peak RSS 3529834496 bytes, zero swaps, revision
335b96d88. All eleven reports are standard. The first digest attempt's broad
ofFn simplification is replaced by a symbolic getElem proof; it is retained
as failed evidence. No limit is raised.

CheckpointBytesLookup adds structural C5 body-block and fixed-width vector
byte lookup, for subsequent aggregation. Final attempt 2 exits 0,
6.080399166792631 s, peak RSS 3656286208 bytes, zero swaps; all four reports
standard (some use fewer than all three axioms). Attempt 1's redundant
bound tactic and unexpanded multiplication identity are retained failures.
It never evaluates the encoded checkpoint or a concrete vector.

## Stage 9: exact query bytes

CheckpointBytesWord.select_bytes proves the checked raw U32 selector returns
exact little-endian bytes for every U32, without a canonical-word premise.
It reuses the E selector's first four symbolic bytes. The remaining seven
limbs are eliminated by structural prefix lookup, not normalization.
CheckpointBytesQuery.query_bytes composes this with the actual sparse body
query dispatch for every one of 22 query words and all four byte positions.
It names no supplied call-success or field-decoder premise.

Word attempt 4: exit 0, wall 10.125658875331283 s, RSS 3619700736 bytes,
zero swaps, revision 335b96d88. Query attempt 1: exit 0,
40.384850832633674 s, RSS 3604365312 bytes, zero swaps, revision 9439e4182.
All four reports are standard. Word attempts 1..3 retain type-transparency,
index-bound and conditional-rewrite failures. Explicit prefix rewrites
replace broad simp. No limit is raised.

The local byte equations now cover every source sparse interval: header,
five digests/state arrays, six wide fields, rho/power, semantic and coordinate
K vectors, all weights, and the query vector. This is **section-complete**,
not a claimed aggregate body_byte/C5 source-state theorem. The independent
18-block raw-field reference plus checksum composition is proved in stage 5.

## Final focused union and precise handoff

CheckpointBytesFreeze attempt 1: exit 0, 6.376390375196934 s, peak RSS
3559882752 bytes, zero swaps, revision 9439e4182c7122bafd45d2edba449da4c178c6e8.
Its 30 union reports include every sparse section family and the unchanged
strictStage/reached_stage/decision consumers. All are standard. This is one
focused compatible-cache union, not a coherent frozen release replay.

The audit checks 19 final modules, all 71 authored theorem reports and 30
union reports, exact source/object/import hashes, source pins, generator
--check outputs, allowed axioms and owned source scope. Maximum accepted
peak RSS is 3813359616 bytes; every accepted attempt records zero swaps.
The native-axiom E attempt is explicitly rejected even though its exit is 0.
All failed attempts remain evidence, not accepted proof results.

**Closed:** complete all-input extracted e_byte execution; exact canonical
E and K selector byte meaning; exact local source equations for every sparse
body section; complete 18-block raw-field reference and checksum equality
with C5; structural lookup laws needed for aggregation. Assumptions are
spelled out: per-selected-field canonicality, header next=10, and 64 weights.
The raw word/query selector needs no canonical-word assumption. No source
call-success law or whole-body equality was introduced as a premise.

**Still open:** the single aggregate source body_byte/C5 theorem, connecting
the concrete extracted Prepared/Accumulator to the Fields reference carrier;
complete exact-width strict-decoder output/rejection semantics; production
Reader/ResumeOps/section/fallible-allocation/Box adoption; the source-stage
byte/decoder join and its six actual digest reads at reached_stage. The
17-zero-byte K counterexample stops the unrestricted strict-K formulation,
not the exact-width production parser target. The allocation model theorem
stops an unconditional success theorem across all reservation states, not
an accepted-source refinement conditioned on actual source success.

The exact next new consumer is CheckpointBytesBody.body_byte_c5, using the
section equations and CheckpointBytesLookup. The final existing endpoint is
OraclePortCkptAbi5Stage.reached_stage through strictStage and then
OraclePortCkptAbi5Decision.decision_observation. NEXT.md keeps
S2S10CallerBinding separate from S1S7S8StateProvenance. Neither is hidden
in P6 or asserted proved. No new checkpoint cone join, AcceptedRunJoin,
headline premise removal or deployed security conclusion is supplied.

No shipped/protected/sibling/existing baseline Lean source changed. No Rust,
Kani, Aeneas, SBF, host env-J, runtime or full frozen release replay ran.
Inherited Kani results are reused only within their original domain; no
whole-function harness was launched. The shipped-source/ELF rebuild trigger
is absent, so no new ELF byte-identity measurement is claimed. No shared
object, root checkout, key/wallet, merge, push or local target/ was touched.
All work is committed locally with plain messages. Recheck the packet with:

    python3 -B tools/ckpt-bytes-20261021/audit.py
