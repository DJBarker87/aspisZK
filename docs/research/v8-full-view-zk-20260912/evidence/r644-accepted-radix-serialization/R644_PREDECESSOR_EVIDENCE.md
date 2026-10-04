# R644 predecessor source and proof evidence bundle

This bundle preserves exact sources and all recorded focused receipts/logs/snapshots for R637, R639, R640, R641, R642, R643 and R644. It is evidence assembly only; no target was recompiled during bundle assembly.

All Lean jobs used the pinned source root `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`, cached workspace `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`, Lean `-j1 -M4500`, and `systemd-run --user --wait --collect --pipe` with MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0 and TasksMax 128. The runner is preserved as `run_focus.py`.

## Selected proof inputs

### R637PackedBitExtraction
- Accepted final run `1791109539861457000`; source SHA `66e1b7c54f682324d451c5e41f066fac900e084056a3327390552b21ef11c681`; exit `0`, wall `0:02.32`, peak RSS `3773728 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R637PackedBitExtraction/1791109539861457000/`.

### R639PackedByteBits
- Accepted final run `1791109540317412000`; source SHA `47c4fe099edab1a5a7f08a3de3ea4e1adcd50009fe0f7f81a31deaebccb0f580`; exit `0`, wall `0:01.74`, peak RSS `3752288 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R639PackedByteBits/1791109540317412000/`.

### R640DecoderExactWords
- Accepted final run `1791109959752267000`; source SHA `0aa14e1969cbbf6dab96a2e3eb62dc1ea0c8a12f8d142676875ac1e0a8577d8d`; exit `0`, wall `0:01.82`, peak RSS `3771272 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R640DecoderExactWords/1791109959752267000/`.

### R641PackedByteConcat
- Accepted final run `1791109864014716000`; source SHA `bf36299be2b0f407c48ea5e45bf81cff737401a36a3725c8978f97e8ad1a23ef`; exit `0`, wall `0:02.12`, peak RSS `3773916 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R641PackedByteConcat/1791109864014716000/`.

### R642SourceScalarWrapper
- Accepted final run `1791110380871330000`; source SHA `4ed35f944799cb273d4fdc220f8e918df89671b3ee1ff46bf577a0a68d38c4a4`; exit `0`, wall `0:01.82`, peak RSS `3764120 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R642SourceScalarWrapper/1791110380871330000/`.

### R643PackedRadixValues
- Accepted final run `1791110216805186000`; source SHA `0c7339bc2c1ad3eb619045922ce4aff622cbc07fbc1ef756b047b03ffe5cd1ed`; exit `0`, wall `0:01.41`, peak RSS `3748888 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R643PackedRadixValues/1791110216805186000/`.

### R644AcceptedRadixSerialization
- Accepted final run `1791110536464503000`; source SHA `a12bdc8470a9923fda1e22e1e1efbd9b08f0ad77c95ad80ad0f3d3e4eff3586c`; exit `0`, wall `0:01.50`, peak RSS `3757896 KiB`, swap `0`. Full receipt and complete #print axioms output are preserved in `attempts/R644AcceptedRadixSerialization/1791110536464503000/`.

## Explicitly excluded experiment

Run `1791108622890866000` for R637 returned exit 0 but its `source_word_masked_extract` axiom list contains eight generated `_native.bv_decide.ax_*` axioms. It is preserved for audit and excluded from the final R637 theorem and this composition chain. Other archived R637 trials using `bv_decide` are likewise not used. The two R639 runs `1791109449569874000` and `1791109530982422000` exited green but have `sorryAx` in the relevant theorem’s axiom report; those are also excluded. The accepted final R637/R639 runs have only standard Lean axioms (except R644’s separate opaque Formatter type dependency noted above).

## R644 accepted decoder bridge

R644 target `AspisV8R19/R644AcceptedRadixSerialization.lean` compiled green in run `1791110536464503000` (exit 0, 1.50s, peak RSS 3,757,896 KiB, swap 0). It proves the accepted decoder output equals the mathematical base-2^31 digits of complete 31-byte little-endian chunks, and accepted digits are all strictly below P. The final accepted theorem depends on `core.fmt.Formatter`; its complete three declaration axiom list is in the receipt. The three failed R644 attempts (`1791110419351937000`, `1791110446718008000`, `1791110488643026000`) are preserved.

## Exact source inputs

The seven files and hashes are in `manifest.json` under `source_inputs`. R637/R639/R641/R642/R643 inputs are scratch copies, not promoted Lean modules. The upstream R623/R624 source files and R640 composition dependency are included as pinned source context.

## Boundary

The included results connect symbolic packed-bit extraction, little-endian byte-window identities, source-shaped U64 word concatenation, the actual scalar mask/cast/list wrapper and radix-2^31 digits. R643 explicitly leaves digit P possible at the unaccepted representation layer. Root’s R644 theorem must use actual accepted-decoder facts to exclude P before calling a representation canonical. No privacy or soundness statement is proved by this bundle.
