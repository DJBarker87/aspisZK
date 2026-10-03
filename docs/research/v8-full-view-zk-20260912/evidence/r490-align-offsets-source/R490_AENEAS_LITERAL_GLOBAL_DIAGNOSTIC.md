# R490 compiler-valued global diagnostic

Scope: read-only diagnosis of the R490 translation failure. No source, projection, or tool changes; no retry/compile.

## Captured declaration facts

- LLBC input: `.r21-scratch/r488-parser-extraction/saved-output-d/R488ActualParser.llbc`, SHA-256 `8b90bc73400b90581ffa626a517dd26b7ef4bb676f83c7bd864693ead75c3bff`.
- R490 selected projection: `.r21-scratch/r490-align-offsets-source/R490AlignToOffsetsSourceSelection.llbc`, SHA-256 `384d170f403306449c7435e81da6050ae3f447b28a9ab0dc881450c9322621af`.
- Projection root Fun20 is `core::slice::[inherent impl]::align_to_offsets::<u8,u32>` and retains Global7 and Global8.
- In the `--consts values` capture, Global7's `value.kind` is literal `Usize(4)` and Global8's is literal `Usize(1)`. Both are compiler-evaluated declarations, not `CCall(FunId(FRegular ...), [])` initializer functions.
- Aeneas failed before producing Lean output: `Invalid_argument "option is None"` at `FunsAnalysis.ml:176` (`Stdlib__Option.get`), exit 2, approximately 0.18 seconds and 57 MiB RSS (saved run receipt/log).

## Why that option is absent

Pinned generated Charon helper `GAstUtils.ml:177-180` defines `init_fun_id_of_global` by matching only `global.value.kind = CCall(FunId(FRegular id), [])`; every other initializer shape returns `None`. Thus it necessarily returns `None` for these two literal-valued globals.

Pinned Aeneas `FunsAnalysis.ml:153-176` handles `RvRef(PlaceGlobal ...)`: it first checks `ExtractBuiltin.builtin_globals_map()`, and if no builtin matches, it calls `Option.get(init_fun_id_of_global global)` to propagate initializer `can_fail`. The observed exception is exactly this fallback on a literal global with no matching builtin.

## Complete use-site inventory in the pinned source snapshot

`rg -n init_fun_id_of_global` over the R439 pinned Aeneas/Charon source copies finds:

1. `FunsAnalysis.ml:176`: effect analysis for a global read; the failing call site.
2. `symbolic/SymbolicToPure.ml:363`: `translate_global` obtains `body_id` with `Option.get` and uses the initializer function's failure information.
3. `Translate.ml:1009`: `export_global` obtains `global_init` with `Option.get`, looks up its translated function body, and derives opacity/loop exports from that body.
4. `GAstUtils.ml:177`: helper definition; only recognizes a regular zero-argument function call initializer.

Hashes of the pinned evidence copies: `FunsAnalysis.ml` `bb46649cb8466a7bf028df8f0baa6af1367e900d6cff0ad4157cab30085fe580`; `SymbolicToPure.ml` `15019f32e7c39cff383cf213fe0747709dbaab8201e8595c138c6f6eeda7bea7`; `Translate.ml` `19f7e1b91e2a066e24c4231322ae3d5a78464c9ad0f56e8d2cb6358a65837ea5`; `GAstUtils.ml` `4631c556d08ed2f4d3c7b9f73087d343651104ac9c01f150199d18087b3ec1a6`; `interp/Interp.ml` `b597a7276d7fd1d6e721f7902ad9f4f03c8281cf581a81521c0ba1031ddba308`.

## Scope of the backend gap

`interp/Interp.ml` computes declarations to extract from the crate's declaration groups, retains referenced global declarations in `global_decls_to_extract`, and visits them while discovering trait methods. That path does not synthesize an initializer function for a literal value. The frontend's downstream global translation is also function-shaped: `SymbolicToPure.translate_global` and `Translate.export_global` require an initializer function body. Therefore guarding/removing only the FunsAnalysis `Option.get` would get past the first crash but would not give the backend a value/body to translate; the two later `Option.get` consumers remain.

A faithful backend extension would need a deliberate literal-global representation/translation (including effect/failure information and global export), wired through all three consumers, or an equivalent generated initializer function supplied by the frontend while retaining exactly the captured literal value. This diagnostic does not choose between those routes or assert that a literal has initializer-call semantics. The existing R488 `--consts` capture without `values` is a distinct LLBC capture shape with initializer functions; using it would change capture policy and needs lead review against the actual source/toolchain contract.

## Proven boundary / next obligation

Proved by inspection: the first `Option.get` has no value for R490 Global7/8; the backend also assumes function-backed globals at two downstream translation sites. Not proved: any semantic equivalence between R488 `--consts` policies, or correctness of modifying/working around Aeneas literal-global support.
