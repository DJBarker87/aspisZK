# Reused field codecs and current mixed leaf encodings

This checkpoint connects exact M31/QM31 values to canonical byte lists and
proves that the model's mixed C1/C2 encodings are injective. The independent
Rust regression checks semantic-record limb boundaries. Neither result is a
proof that the complete Rust verifier implements the Lean protocol.

## What is checked

`ListFieldCodec` wraps the existing exact-length byte decoder. It proves
both decode-after-encode and encode-after-successful-decode, for four-byte M31
and sixteen-byte QM31 values. The latter preserves every input byte; it does
not merely identify two values modulo the field characteristic.

`ExactLeafFieldCodec` composes those facts with the existing literal
`Fin P`/`ZMod P` and four-limb/tower equivalences. Its signatures use the same
`ExactTowerBase.M31Exact` and `QM31Exact` as the current algebraic work.
Successful decoding therefore has one canonical byte representation in this
model. The encoder lengths and injectivity are also checked.

`MixedLeafEncoding` uses the current slot-major layout:

| Encoding | Contents per slot | Slots | Bytes |
| --- | --- | ---: | ---: |
| C1 | 26 M31 values, followed by lane 28's QM31 value | 4 | 480 |
| C2 | lane 26 and lane 27, both QM31 | 4 | 128 |

Each slot encoder and full leaf encoder has a proved length and injectivity
statement. The generic fixed-width flattening theorem composes per-field
injectivity; the C1 slot uses its fixed 104-byte M31 prefix to separate the
trailing 16-byte QM31 value. The layouts were compared with
`host_commitment.rs` and `verifier.rs`; that comparison is a source review,
not a Lean source-semantics theorem.

## Existing proofs retained under the resource cap

The retained byte declarations come from `V5ComponentCRejectionSampler`,
`V5ComponentCQM31Representation`, `K1.V7Tag73SemanticTranscriptBridge`, and
`V5MerkleConsumedValueBridge`. The exact-limb block comes from
`V5ComponentCQM31TowerExact` and uses the already-retained `ExactTowerBase`.

Two full bridge attempts and two import-only diagnostic probes exceeded
Lean's configured memory threshold. The import probes isolated the cause
from the new proofs. The replacement retains the existing declarations in
narrow modules instead of loading the full sampler/transcript/Merkle
capstones. The cap remains `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`.

`tools/retain-field-byte-codec.py --check` verifies the pinned original
files, extracted declarations, and the three permitted namespace-qualifier
replacements. `tools/retain-exact-limb-codec.py --check` likewise verifies
its block, with one explicitly recorded proof adaptation: two finite-index
equalities close with `congrArg x (Fin.ext rfl)` after the alias context
changes. The statements and premises are unchanged. The old files remain
untouched. This is source retention with rechecked proofs, rather than an
import of the original large modules.

## Verification evidence

Source base: `d08448d3a0bcd78a777217eaa6594fc658115cc2`.
The combined `LeafCodecCheckpoint` exited 0 in 1.31 seconds, at 3,301,336 KiB
peak RSS, with zero swap. Its 34 declaration audits use only `propext`,
`Classical.choice`, and `Quot.sound`. Four retained-limb declarations are
audited here; the separate retained-limb compile printed no axiom reports.
Receipts, final sources/objects, failed attempts, import probes, and the
uncompiled empty staging artifact are recorded in
`evidence/lean-leaf-codec-20261014/`.

The added Rust test,
`semantic_rows_reject_noncanonical_limbs_at_every_wide_position`, covers all
426 value positions across rows 14–26. At every limb it rejects `P`, `P+1`,
and `u32::MAX`; low-half `P-1` values are accepted, while a high-half limb
of one is rejected by the current semantic subset rule. It passed on a new
506-file NUC snapshot in 2.54 seconds, with a 194,016 KiB GNU-time peak RSS
and zero swap, under the same 4G/6G/zero-swap limits. Its archive, exact test
diff hash, logs and independent root audit are in
`evidence/parser-all-limbs-20261014/`. This test exercises `parse_record`,
not the mixed leaf decoder or the authenticated checkpoint lifecycle.

## Follow-up and remaining requirements

[LEAF-DECODER-CHECKPOINT.md](LEAF-DECODER-CHECKPOINT.md) now supplies strict
480/128-byte model decoders and their encoder/offset connections. The recovered
Merkle bytes must still
be connected to the typed candidate word, including the actual index and
lane order. Current Rust parsing, checkpoint provenance, authenticated
resume, arithmetic, and settlement need their source correspondence.
Universal privacy and the full adaptive Fiat–Shamir argument remain
separate security obligations.
