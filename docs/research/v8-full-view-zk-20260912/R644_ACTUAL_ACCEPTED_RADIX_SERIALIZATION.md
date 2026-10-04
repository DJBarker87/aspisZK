# R644 actual accepted radix serialization

Verified and promoted byte-for-byte from the focused successful builds listed below. No unchanged check was repeated.

`accepted_radix_serialization` proves that every accepted actual generated `r55_decode_into` result, for every output width `N.val ≤ 104`, returns exactly the mathematical base-2^31 digits of the complete 31-byte little-endian chunks returned by actual `chunks_exact`. Every accepted digit is strictly below `P = 2147483647`. The initial output array and input bytes are arbitrary; acceptance supplies the complete destination coverage, header, chunk sizes, rejection condition and writes. Both selected quotient input sizes, 104 and 48, are covered.

Each chunk digit is defined as `chunkBits248.toNat / 2^(31*j) % 2^31` for all eight positions. The proof connects actual scalar mask/cast and four source U64 reads (offsets 0, 8, 16 and 23, last shifted by eight) to the full byte packing and those independent mathematical digits. It preserves the possible forbidden digit P in the representation and excludes it only through actual acceptance. It does not assume canonical input, valid bytes, successful internal operations, or a mathematical interpretation of an opaque decoder loop.

This proves the accepted serialization boundary in the generated source and pinned Aeneas scalar/array model. It does not prove the complete 38-term quotient dot product, the coefficient constructor, native compiler/interpreter adequacy beyond imported correspondence, the callback, universal C1/H1/G compatibility, the published-view simulator, adaptive shared-oracle laws, soundness, or 100-bit security.

The first remaining quotient proposition is complete actual `r83_mixed_limb` execution equal to the intended 26 C1 plus 12 C2 products under justified canonical source inputs/coefficients, then its four-coordinate loop and actual coefficient constructor. No verifier source, challenge size, query count, authentication, canonical rejection, security parameter or negative example changed. Saved CU results remain 999,790 / 999,532; no CU benchmark or unchanged regression was run.

## Focused verified runs

| Exact target under AspisV8R19 | Run | Source revision | Source SHA-256 | Exit | Wall | Peak Lean RSS KiB | Swap |
|---|---|---|---|---|---|---|---|
| `R637PackedBitExtraction.lean` | `1791109539861457000` | `e32255afb947ea19273553777273c56c60e3b28c` | `66e1b7c54f682324d451c5e41f066fac900e084056a3327390552b21ef11c681` | 0 | 0:02.32 | 3773728 | 0 |
| `R639PackedByteBits.lean` | `1791109540317412000` | `e32255afb947ea19273553777273c56c60e3b28c` | `47c4fe099edab1a5a7f08a3de3ea4e1adcd50009fe0f7f81a31deaebccb0f580` | 0 | 0:01.74 | 3752288 | 0 |
| `R640DecoderExactWords.lean` | `1791109959752267000` | `e32255afb947ea19273553777273c56c60e3b28c` | `0aa14e1969cbbf6dab96a2e3eb62dc1ea0c8a12f8d142676875ac1e0a8577d8d` | 0 | 0:01.82 | 3771272 | 0 |
| `R641PackedByteConcat.lean` | `1791109864014716000` | `e32255afb947ea19273553777273c56c60e3b28c` | `bf36299be2b0f407c48ea5e45bf81cff737401a36a3725c8978f97e8ad1a23ef` | 0 | 0:02.12 | 3773916 | 0 |
| `R642SourceScalarWrapper.lean` | `1791110380871330000` | `1b039ba01da4db969ffecf479b46e72c7a52d55d` | `4ed35f944799cb273d4fdc220f8e918df89671b3ee1ff46bf577a0a68d38c4a4` | 0 | 0:01.82 | 3764120 | 0 |
| `R643PackedRadixValues.lean` | `1791110216805186000` | `1b039ba01da4db969ffecf479b46e72c7a52d55d` | `0c7339bc2c1ad3eb619045922ce4aff622cbc07fbc1ef756b047b03ffe5cd1ed` | 0 | 0:01.41 | 3748888 | 0 |
| `R644AcceptedRadixSerialization.lean` | `1791110536464503000` | `1b039ba01da4db969ffecf479b46e72c7a52d55d` | `a12bdc8470a9923fda1e22e1e1efbd9b08f0ad77c95ad80ad0f3d3e4eff3586c` | 0 | 0:01.50 | 3757896 | 0 |

All runs used pinned Lean 4.32, cached workspace, `lake env lean -j1 -M4500`, independent systemd scopes with MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0 and TasksMax=128. GNU time reports Lean-child RSS; wrapper cgroup MemoryPeak is not an aggregate Lean RSS measurement. Exact commands, all source snapshots, complete logs, receipts and source/dependency pins are saved in `evidence/r644-accepted-radix-serialization/`.

## Complete accepted axiom output

```text
'AspisV8R19.R637PackedBitExtraction.source_word_masked_extract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R637PackedBitExtraction.source_word_bit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R637PackedBitExtraction.packed_lsbD' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R637PackedBitExtraction.mask_bit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R637PackedBitExtraction.getLsbD_false_of_ge' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R639PackedByteBits.eight_from_le_bytes_bit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R640DecoderExactWords.decoder_accepted_exact_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
'AspisV8R19.R640DecoderExactWords.wordsOfChunks' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R640DecoderExactWords.chunks_filled_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
'AspisV8R19.R641PackedByteConcat.bytePack_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R641PackedByteConcat.bytePack_high' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R641PackedByteConcat.packed_bytes_concat' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.AspisV8R19.R642SourceScalarWrapper.0.AspisV8R19.R642SourceScalarWrapper.mask_cast_bv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R642SourceScalarWrapper.block_word_matches_maskedLow32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R643PackedRadixValues.radixDigit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R643PackedRadixValues.masked_source_radix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R644AcceptedRadixSerialization.block_radix_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R644AcceptedRadixSerialization.words_radix_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R644AcceptedRadixSerialization.accepted_radix_serialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
```

Only the standard logical axioms occur in the pure bit/scalar/serialization bridges. Whole decoder execution inherits the previously documented opaque `core.fmt.Formatter` type. No accepted theorem uses `sorryAx` or generated native `bv_decide` axioms. All unsuccessful and excluded experiments remain archived, including the exit-zero native-axiom R637 experiment and the R639 experiments whose axiom output contained `sorryAx`; they are not part of the accepted chain. The manifest names the exact accepted runs.
