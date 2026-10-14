# Field parser extraction record

This note records the pinned Charon/Aeneas extraction attempts in [the evidence bundle](evidence/field-parser-extraction-20261014/README.md). The bundle archive contains 69 members; every member hash in its manifest and all 10 `SHA256SUMS` entries verified. The archive SHA-256 is `2f7698ed64c72cb29f79e5309a63ad7c8ecd2aecec99441f5fc5f8866320d254`.

The extracted inputs are pinned to source revision `e2f01d0fc9aaf70bbf99c86c7764526233e0be5a`. The complete `field.rs` and `field/wide_exact.rs` files are retained unchanged and match hashes `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68` and `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea`.

Attempt **a** translated the M31, CM31, and QM31 parser bodies. Its generated external template contains three opaque core-helper axioms: `Result::ok`, `Option::Try::branch`, and `Option::FromResidual::from_residual`.

Attempt **b** asked Charon to include `core::option` and `core::result`. LLBC extraction succeeded, but Aeneas translation exited 2 with `Inconsistent state` while interpreting the `Result::ok` match at `/rustc/library/core/src/result.rs:713–717`. The LLBC and failure logs are preserved.

Attempt **c** translated only the M31 parser and probe successfully, without opaque Option/Result helpers. The retained [ExtractedM31Parser.lean](lean/ExtractedM31Parser.lean) concatenates its generated type and function declarations, and [the source checker](tools/check-extracted-m31-parser.py) verifies those declaration bodies against the pinned generated files. The wrapper imports the two cached Aeneas modules required by those declarations instead of the missing umbrella module. The retained parser and its refinement are now Lean-checked as described below.

Attempt **d** adds monomorphization to b. Extraction succeeds, but translation fails at the same helper. Its separate [evidence bundle](evidence/field-parser-extraction-d-20261014/README.md) preserves all 20 input/output/log files, excluding compiler caches. Attempt e below changes the MIR stage and reproduces that failure.

## Checked M31 contract

[M31ParserRefinement.lean](lean/M31ParserRefinement.lean) applies the old
`SamplerWordBridge.four_bytes` result through `AeneasWordCodec`, then proves
the extracted parser equals the retained V5/K1 canonical decoder for every
four-byte word. There is no canonical-input premise: rejected words are
covered as well as accepted words.

[M31ParserCanonicality.lean](lean/M31ParserCanonicality.lean) derives exact
acceptance below `P = 2^31-1`, exact rejection at or above P, and the literal
little-endian value of every successful parse. [M31ParserArray.lean](lean/M31ParserArray.lean)
reuses the old `SqueezeOracleBridge.word_roundtrip` theorem to cover every
Aeneas four-byte array, without a representation premise.

All five focused targets passed on the pinned NUC workspace in separate
4 GiB high / 6 GiB maximum / zero-swap scopes. Their source revision, exact
source hashes, failed predecessors, logs, receipts, dependency pins, and
compiled objects are preserved in the [Lean evidence bundle](evidence/lean-m31-parser-20261014/README.md).

| Target | Exit | Wall seconds | Peak RSS KiB | Swap | Axiom reports |
|---|---:|---:|---:|---:|---:|
| `R1ExtractedM31Parser` | 0 | 1.34 | 2,557,824 | 0 | 3 |
| `R1M31ParserRefinement` | 0 | 1.65 | 3,803,192 | 0 | 1 |
| `R1M31ParserCanonicality` | 0 | 3.17 | 3,779,396 | 0 | 3 |
| `R1M31ParserArray` | 0 | 2.61 | 3,775,020 | 0 | 3 |
| `R1M31ParserCheckpoint` | 0 | 1.57 | 3,763,860 | 0 | 12 |

Every successful audit contains only standard Lean axioms. The final
checkpoint imports the four components and audits their results together
with the reused word/byte theorems. No runtime source changed.

This proves the contract of the retained generated M31 definitions. It does
not prove Charon, Aeneas, Rust compiler correctness, the Aeneas standard-library
models, or equality to deployed SBF execution. CM31/QM31 helper translation,
exact caller slice widths, WideExact parsing, leaf/caller composition, and
checkpoint/account correspondence remain separate source obligations. The
complete privacy and adaptive Fiat–Shamir security conclusions remain open.

## Drop-cleanup translation diagnosis

The failing LLBC is not missing the `Result` enum declaration or its variants. In the pinned d artifact (`R1FieldParser.llbc`, SHA-256 `ce387c75d46f6f37bda692a5ac43486cf86cb7e7b241e2aeb8de2b29019f1d25`), `core::result::Result::ok` has a first match whose `Ok` arm moves the payload into `Some`, followed by a cleanup match on `self`: the `Ok` arm is empty and the `Err` arm drops `self` (the Rust span is `core/result.rs:713–717`). This is the partially-moved-enum case described in pinned Aeneas `InterpStatements.ml` immediately above `eval_switch_raw`'s match handling. That evaluator accepts bottom only when all targets have the same LLBC statement-kind sequence; here the empty arm and `Drop self` arm differ, so the value reaches the `Inconsistent state` fallback at line 1286. The Aeneas source revision is `1d31b733124394b34195a6abdb3bca7a312d46f1`; relevant code is `src/interp/InterpStatements.ml:1242–1286`. `src/interp/InterpExpressions.ml:93–113` confirms that the discriminant accessor returns the raw place value for the match evaluator.

The pinned Charon CLI advertises `--mir built`, `promoted`, `elaborated`, and `optimized`. Its help describes `promoted` as before drop elaboration, `elaborated` as the first MIR stage with all runtime information, and `optimized` as after optimizations while noting Charon disables the optimizations it can and that this is sensibly the same as elaborated MIR. Attempt b/d used `--mir built`; using `--mir promoted` is a supported way to avoid drop-elaboration-generated control flow, but it also omits runtime drop information and is not evidenced as semantics-preserving for this parser. `--mir optimized` is supported, but the pinned help provides no evidence that it removes this cleanup switch. The only drop-related Charon flags advertised are `--precise-drops` (retain precise drop behavior and add `Destruct` bounds) and `--desugar-drops` (rewrite precise drops as `drop_glue(&mut p)` calls); neither is a no-op-drop elimination pass. No supported Charon flag or existing extraction attempt has been found that removes this specific nonuniform cleanup match while preserving the source semantics. No new compile or extraction was run for this diagnosis.

### Optimized-MIR diagnostic e

Attempt **e** changed only Charon's MIR stage from `built` to `optimized`; it retained the same source, includes, monomorphization, and start item as d. Charon exited 0 and Aeneas exited 2 with the same `Result::ok` cleanup-match failure, so this pinned optimized-MIR run did not remove the failing control flow. The complete separate artifact is [evidence/field-parser-extraction-e-20261014](evidence/field-parser-extraction-e-20261014/README.md): its archive SHA-256 is `d2044674a6be21ae27a5b7703eb8bc6639b26a9b41344bd0a83c6d0838d6045f`; the e LLBC SHA-256 is `62e55ec16d6292ef40d958cae639a4e8d2c8cb4c5a3187de76bf91251d832a1e`.

The concrete `Result::ok` use is reached from `CM31::from_le_bytes` at the pinned source `field.rs:410–413`: the `try_into()` result is contextually `Result<[u8; 4], core::array::TryFromSliceError>` before `.ok()?`. The same conversion occurs for its second M31 limb and in the QM31 parser. In pinned nightly core, `TryFromSliceError` is a unit struct deriving `Copy` and `Clone` at `core/src/array/mod.rs:183–185`; the successful payload is a four-byte array. Thus the payload types have no user-defined destructor in this path. This source fact does not prevent Charon from retaining a cleanup discriminant match for the generic `Result::ok` body.
