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
