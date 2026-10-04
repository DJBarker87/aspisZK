# R614 shift-count type mismatch inventory (read-only analysis; exact printer patch prepared separately)

The current generated `reduce_chunk` body fails Lean elaboration because its source-level shift count is a signed `i32` literal while Aeneas's unsigned wrapping-shift API requires `U32`.

## Pinned source and translation evidence

- Frozen R604 LLBC input: `/home/dombarker/project-offloads/aspis-r604-combine-beta-generic-20261004-b/R604CombineBetaGeneric.llbc`, SHA-256 `5391af65767eee12ff76fbddbe2be730f4cad8af24d526f6030140539fc4ec44`.
- Its embedded file 0 is named `../query_arithmetic.rs`, embedded source SHA-256 `545e1dac8421bfd2bc2635590d0d6e1065a58c0f02924f25c8228f44d0a3590d` (24,357 bytes). The `reduce_chunk(raw: u64)` body contains `raw >> 31` at source line 9; the R604 LLBC declaration has source span file 0, lines 7–12, `def_id=125`, fully qualified as `aspis_v8_performance_host::query_arithmetic::reduce_chunk`.
- The LLBC operation is `BinaryOp [Shr Wrap]` with lhs `Copy Local` of the function input's U64 type and rhs `Const Literal Scalar Signed [I32,31]` (rhs type node `Deduplicated 2201`). The source expression is an unsigned U64 right shift with a nonnegative signed-i32 count literal.
- R614 generated artifact: `generated/AspisR614SelectedCombineBeta/Funs.lean`, SHA-256 `44014429b888c2bab18dd7212d4a4d941a2a8c4c6dffff3448fd8f7abe747dca`, from archive SHA `0dd247fc802474d0ee29623e396820bea0260e5e394aadd423ebbb30627fa6f6`. At lines 75–80, generated code is:
  `def query_arithmetic.reduce_chunk (raw1 : Std.U64) : Result Std.U64 := ...`
  `let i2 ← lift (Std.U64.wrapping_shr raw1 31#i32)`.
  Translation used `ops_to_function_calls=true`; this is the emitted type mismatch, not a Lean theorem failure.

## Pinned API and existing compatibility results

- Pinned Aeneas source `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/Aeneas/Std/Scalar/WrappingOps/Shr.lean`, source-tree commit `b59d5188c082f704a418c7cb4e52ad69328002d1`, file SHA-256 `34837809e785ceeaf47b042afd7fb747f68ce474c30f29670e9694fe129f1714`. Its declaration is `UScalar.wrapping_shr (x : UScalar ty) (s : U32)` and computes `x.bv.ushiftRight (s.val % ty.numBits)`. The generated `31#i32` does not match the required `U32` argument.
- `R498UsizePrimitiveNames.lean` (SHA `cbe454ed55969c626c158b8a543ee607411a63d3a3b864572fd584c4f2bed3fc`) aliases only Usize `div`/`rem`; it contains no shift-count compatibility API.
- `R158WordBounds.lean` (SHA `fd658946cad404c92705434a59be6167a6767a1eb5757671643ce489b26b631c`) proves `wrapping_shr31_value` for `(U64.wrapping_shr x 31#u32)`. It does not relate an I32 shift argument to U32.
- Earlier `AspisR249R110Raw.lean` (SHA `f38d892beef83cba109b007a5d5b6851629ead6acc736d2fbff1c25a530f72cd`) emits `31#u32` in the adapted raw file and proves ground `count_thirty_one : (31#i32 : I32).bv.toNat = (31#u32 : U32).val` (also for 1 and 30). This is a proved equality of these positive constant count values; it is not a general conversion theorem for arbitrary signed counts or an execution correspondence for this new R604 extraction.

## Mapping locations

- Candidate/original `src/symbolic/SymbolicToPureExpressions.ml`, lines 715–722, builds `Shl/Shr (overflow_mode, ty0, ty1)` using both operand types. File SHA-256 `126eec257214698d71b16b90b01e0184a0d2f38db2266eaec3c2776f62fa537d`.
- Candidate/original `src/extract/Extract.ml`, lines 648–671 (SHA-256 before proposed patch `caf4139ec75cdfb721ed44e823e49134927035b1d0655a050d07c06e3fc0cd14`), selects `Std.<lhs integer type>.wrapping_shl/shr` using `arg0.ty`, then sends `arg1` through the generic printer unchanged. Thus a source-typed `I32` literal is emitted as `#i32` even though Aeneas's wrapping op expects U32.

## Lead-authorized narrow repair proposal

In only the Lean `Shl(OWrap,...)` / `Shr(OWrap,...)` printer arm, inspect the existing typed rhs without reevaluating it. For exactly `arg1.ty = TLiteral (TInt I32)` and `arg1.e = Const (VScalar (SignedScalar (I32,n)))`, when lhs type is exactly U32 or U64 and `0 ≤ n < 32` or `0 ≤ n < 64` respectively, print the same nonnegative integer `n` with existing `extract_literal` as `VScalar (UnsignedScalar (U32,n))`. Fall back to the existing `extract_expr arg1` for every other shape/operator/backend. This is a literal-only Lean printer compatibility change, not a Rust source/body change or a general cast. No build or translation was run for this inventory.
