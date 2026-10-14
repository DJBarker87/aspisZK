# Mixed C1/C2 leaf decoder model checkpoint

The new mathematical byte-list model defines strict constructive decoders for
the existing mixed C1 and C2 encodings. A successful decode is equivalent to
the input being exactly the literal encoder output for the decoded value, and
success fixes the input lengths to 480 bytes for C1 and 128 bytes for C2.
These statements close the arbitrary mixed-leaf decoder gap recorded in
[LEAF-CODEC-CHECKPOINT.md](LEAF-CODEC-CHECKPOINT.md) at the model level.

For C1, each 120-byte slot consists of 26 strict four-byte M31 decodes in the
first 104 bytes, followed by one strict 16-byte QM31 decode from the remaining
bytes. Four slots give the 480-byte leaf. For C2, each 32-byte slot contains
two strict 16-byte QM31 decodes; four slots give 128 bytes. The field codecs
require their exact byte widths and canonical values. The roundtrip theorems
therefore imply that successful decoding leaves no trailing bytes.

The proof is split across seven green component modules: `FixedWidthSlice`
(2 audited declarations), `FixedWidthReconstruction` (1), `MixedLeafSlices`
(5), `FixedWidthDecoder` (2), `MixedLeafDecoder` (12),
`FixedWidthDecodedSlices` (1), and `AeneasWordCodec` (1). The generic
`FixedWidthDecodedSlices.decode_eq_some_iff` theorem relates recursive
fixed-width parsing to exact reads at each byte offset, using only uniform
encoder width, decode-after-encode, and successful-decode byte recovery
premises. The right-hand side includes the full input length `n * k`; the forward
direction derives that length, and the converse reconstructs the complete
encoder output from the per-offset reads.
`FixedWidthReconstruction.slices_flatten` handles arbitrary element types and
includes zero block count and zero block width.

`AeneasWordCodec.aeneasWord_val_eq` reuses the earlier
`AspisV8R19.SamplerWordBridge.four_bytes` identity from
[SamplerWordBridge.lean](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWordBridge.lean).
It identifies the mathematical Aeneas little-endian U32 value with the
retained word decoder's value for a four-byte word. This is a representation
identity, not a proof that the current verifier caller reaches this decoder.

The combined `LeafDecoderCheckpoint` audit is green: source SHA-256
`ef6d5c54ad3c5c9bad049f216cc1483f2adee8b0b2b174e97a4f26fa08276940`, exit 0,
1.69 seconds, peak RSS 3,783,780 KiB, zero swap, with `MemoryHigh=4G`,
`MemoryMax=6G`, and `MemorySwapMax=0`. All 24 declaration audits report only `propext`, `Classical.choice`, and
`Quot.sound` (or a subset). The [combined evidence bundle](evidence/lean-leaf-decoder-20261014/README.md)
preserves all 22 attempts: 14 failed proof attempts and 8 final targets, with
48 successful axiom reports including the checkpoint. It includes exact
snapshots, receipts, pinned runners and the eight final objects; the root
audited these against current sources and the unchanged 14 runtime pins.
The source base is `8b62ca762b89b5af8f131d1c97a5c6d400df2a6b`.

These results concern a Lean byte-list parser and its mathematical encoders.
They do not establish correspondence with Rust `Option` handling, range
checks, offsets, callers, Merkle recovery, checkpoint provenance, or execution
behavior. They make no source-refinement, Fiat–Shamir, privacy, or security
closure claim.
