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
