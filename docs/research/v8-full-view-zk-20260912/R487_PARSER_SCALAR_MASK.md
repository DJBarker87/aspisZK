# R487 parser scalar-mask arithmetic bridge

R487 compiled successfully in the pinned Lean 4.32 cached workspace. The promoted Lean target matches the successful source snapshot byte for byte. Compilation source revision: `9f31daf4883e90d8b084cc621f524176c9b8e3a3` (`research/v8-r64-guarded-m31-20260929`). Target SHA-256: `9301ed7b50d17b742a38bc4bc537c781153240c065b5110fb88a698783384fe7`.

## Proved boundary

R487 bridges pinned Aeneas `U32` scalar operations—bitwise OR, wrapping addition, and checked right shift by 31—to the R486 32-bit bitvector mask. It proves the list-fold bridge for every `U32` word, including noncanonical bit patterns. For an arbitrary initial mask, the scalar shift accepts exactly when that mask's top bit is initially clear and every word value is below `2147483647`; a separate theorem specializes the initial mask to zero. This replaces the earlier zero-literal rewrite attempt with a general initial-mask invariant.

The bridge covers arithmetic only. It does not prove `align_to`, `chunks_exact`, parser loop execution, `Vec::push`, the byte-memory image or returned parser result, input length checks, or actual parser success/error behavior. In particular, the input length 699 / 11,184-byte parser instance is not closed by these results. The first remaining proposition is the actual parser result-image correspondence for its alignment/chunk/fold/push execution, including lengths and failures. This milestone makes no native-source privacy or end-to-end security claim.

## Compilation record

Exact target: `AspisV8R19/R487ParserScalarMask.lean`. Command: `lake env lean -j1 -M4500` in the pinned cached workspace, under `systemd-run --user --wait --collect --pipe` with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Peak RSS is GNU time's Lean-child RSS in KiB.

- Successful run `1791040115116232000`: exit 0; wall 1.48 s; peak RSS 3,714,164 KiB; swap 0.
- Failed run `1791039924646457000`: exit 1; wall 1.38 s; peak RSS 3,698,948 KiB; swap 0; recorded a failed rewrite and `sorryAx`.
- Failed run `1791039995636898000`: exit 1; wall 11.23 s; peak RSS 3,697,192 KiB; swap 0; recorded type mismatches and a deterministic 200,000-heartbeat timeout during elaboration.
- Failed run `1791040063429104000`: exit 1; wall 1.42 s; peak RSS 3,700,036 KiB; swap 0; recorded a failed symbolic rewrite and `sorryAx`.

No memory cap was raised between the attempts. All exact source snapshots, receipts, and logs are retained in `evidence/r487-parser-scalar-mask/`.

## Complete successful `#print axioms` output

```text
'AspisV8R19.R487ParserScalarMask.scalarStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.scalarAccumulated' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.scalarStep_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.scalarAccumulated_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.canonical_scalar' does not depend on any axioms
'AspisV8R19.R487ParserScalarMask.scalarShift_exact' depends on axioms: [propext]
'AspisV8R19.R487ParserScalarMask.scalarShift_accepts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.scalar_mask_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R487ParserScalarMask.scalar_mask_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`SHA256SUMS.txt` covers the promoted target, this report, and the exact successful and failed run artifacts.
