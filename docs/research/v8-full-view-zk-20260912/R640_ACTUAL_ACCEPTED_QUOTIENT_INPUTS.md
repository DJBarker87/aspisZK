# R640 actual accepted quotient inputs

Status: **Verified; promoted byte-for-byte from the saved successful focused builds.**

The paired result records what an accepted actual `query_arithmetic.combine_beta` entails before the opaque beta loop: both fixed-size decoders accepted, their words are canonical, and the decoder output is the complete source-extracted list of eight words per 31-byte chunk. This is a narrow source-model result for quotient inputs.

R638 (`AspisV8R19.R638CombineAcceptedInputs.combine_accepted_inputs`) derives from an accepted actual wrapper result two accepted `r55_decode_into` executions, with arrays of 104 and 48 `U32` values; every returned word is below `P = 2147483647`; and the exact `combine_beta_loop` result is the accepted wrapper output. The loop itself remains opaque.

R640 (`AspisV8R19.R640DecoderExactWords.decoder_accepted_exact_words`) proves that an accepted complete decoder result equals `wordsOfChunks` over the source `ChunksExact` list, retaining the complete chunk execution, destination updates, and error-preserving decoder bridge imported through R635. It applies to every accepted `N ≤ 104` result and does not assume success in its supporting execution theorems.

This does **not** prove mathematical radix serialization, the full 38-term dot product, native execution beyond the imported source-model correspondence, the entire callback, privacy, or soundness. The next missing work is R637/R639/R641/R642 byte-packing composition for complete mathematical radix serialization, followed by R616’s actual 38-term dot product.

## R638 focused history

Target: `AspisV8R19/R638CombineAcceptedInputs.lean`.

- `1791109100523845000`: exit `1`, wall `0:01.53`, peak RSS `3744012 KiB`, swap `0`, source SHA-256 `913027b9eea1d27cf4a8fb9dfe8f6a7928edc0110237658cd4fa6928740a9fd7`.
- `1791109118173897000`: exit `1`, wall `0:01.69`, peak RSS `3743900 KiB`, swap `0`, source SHA-256 `23e9b38e88b376d8ba9beb197da3efebc5cec1cf4374b00ecebb6f8cbca74a98`.
- `1791109218420655000`: exit `0`, wall `0:01.67`, peak RSS `3755960 KiB`, swap `0`, source SHA-256 `c84e75b332f1739a1c5076b2eba2297d73054d6ded5ac0bd551bff4e20336a4a`.
- `1791109244935464000`: exit `1`, wall `0:01.61`, peak RSS `3743548 KiB`, swap `0`, source SHA-256 `de20c9799fbf640dc31d890e81d5f21787245de9756c9b5c47f1c935623b98ad`.
- `1791109259802740000`: exit `0`, wall `0:01.62`, peak RSS `3758464 KiB`, swap `0`, source SHA-256 `a2b4beaf79f26e8b8ffa2e4c000268f270adfaa5586b4661b60e6fe95c1cde75`.

Final R638 green result: `1791109259802740000`. Axioms: `[propext, Classical.choice, Quot.sound, core.fmt.Formatter]`.

## R640 focused history

Target: `AspisV8R19/R640DecoderExactWords.lean`.

- `1791109482834888000`: exit `1`, wall `0:01.61`, peak RSS `3756436 KiB`, swap `0`, source SHA-256 `582d7d1f5b7e14db8fd900ed6e5dc302202d881c4c48aa57119d91be6b0889e4`.
- `1791109574286948000`: exit `0`, wall `0:01.74`, peak RSS `3773320 KiB`, swap `0`, source SHA-256 `4e5ca4ca718c22281292ec56e43ba3a5a4116cdc6e7813bd2ae80ee7ab08ed29`.
- `1791109959752267000`: exit `0`, wall `0:01.82`, peak RSS `3771272 KiB`, swap `0`, source SHA-256 `0aa14e1969cbbf6dab96a2e3eb62dc1ea0c8a12f8d142676875ac1e0a8577d8d`.

Final R640 green result: `1791109959752267000`. Complete ordered axiom reports:

- `decoder_accepted_exact_words`: `[propext, Classical.choice, Quot.sound, core.fmt.Formatter]`.
- `wordsOfChunks`: `[propext, Classical.choice, Quot.sound]`.
- `chunks_filled_output`: `[propext, Classical.choice, Quot.sound, core.fmt.Formatter]`.

## Reproducibility

Both final runs used source revision `e32255afb947ea19273553777273c56c60e3b28c`, the pinned source root `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`, cache `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`, Lean `-j1 -M4500`, MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, and TasksMax 128. The receipts, source snapshots, full logs, direct import copy, runner, and checksums are in `evidence/r640-accepted-quotient-inputs/`.

Canonical source paths are listed in `evidence/r640-accepted-quotient-inputs/PUBLISH_PATHS.json`. The packaging record preserves its original scratch-only status; the lead subsequently checked every checksum and promoted the exact verified sources without repeating unchanged checks.
