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
