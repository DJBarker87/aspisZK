# Usize division/remainder name and source check

No source or Lean files were changed or compiled for this check. It reconciles the operation names emitted into the R490 focused generated `Funs.lean` with the pinned Aeneas scalar definitions, and records the cached imports available to the focused runner.

## Name generation used by the R493/R497 tool

Tool build source is Aeneas source revision `56a931fc3879354a2fa584e73bd0a1d412714851` plus the reviewed R491/R493 source patches. In that isolated tool workspace, `src/extract/ExtractBase.ml` has SHA256 `7209c8454b68c63a838efadb52e9b82ad58a646eabebcfb58c6b4161ee92a0c0`. Its `int_name` maps `Unsigned Usize` to the string `Usize`; its `named_binop_name` emits `int_name ty ^ ".div"` for `Div` and `int_name ty ^ ".rem"` for `Rem` when the backend is Lean. The current cached source checkout has revision `b59d5188c082f704a418c7cb4e52ad69328002d1` and `src/extract/ExtractBase.ml` SHA256 `860a440dd86fbe993ce7b42b5876d2cf0c9243f95f8573d2f1191e35ec95b83a`; these exact function excerpts are identical to the isolated tool workspace excerpt despite the whole-file hash difference.

The tool's `src/symbolic/SymbolicToPureExpressions.ml` maps source `Expressions.Div om` and `Expressions.Rem om` to typed `Div` and `Rem`; its candidate SHA256 is `126eec257214698d71b16b90b01e0184a0d2f38db2266eaec3c2776f62fa537d`. The resulting R490 `Funs.lean` contains `Usize.div` and `Usize.rem` calls. The names therefore come from the typed integer operation plus the Lean backend's integer-name renderer, not from manually substituted semantics.

## Pinned Lean definitions and exact specialization

The Std source/library is a separate pin: Aeneas checkout `b59d5188c082f704a418c7cb4e52ad69328002d1`, at `toolchain/aeneas-full/backends/lean`. The actual definition files are clean at this revision and have these SHA256 values:

- `Aeneas/Std/Scalar/Core.lean`: `ceba1982545251f02d6e286abf23d01f4d2a691fe6934149f3a42d4a051af81e`
- `Aeneas/Std/Scalar/Ops/Div.lean`: `74677262c944dc89a3a96e56f467679a565f6aaa9fd09372f24266305175186`
- `Aeneas/Std/Scalar/Ops/Rem.lean`: `b000ee67e059504dbe839b2cd3f35222d364e078d0b184ab373a67658cd2a580`

`Core.lean` defines `Usize := UScalar .Usize` (line 654). `Ops/Div.lean` defines `UScalar.div {ty} (x y : UScalar ty) : Result (UScalar ty)` and returns `divisionByZero` when the divisor is zero (line 15). `Ops/Rem.lean` defines the same typed-result specialization for `UScalar.rem`, also returning `divisionByZero` for zero (line 14). These pinned files do not define `Usize.div` or `Usize.rem` names. Thus wrappers `Usize.div (n d : Usize) := UScalar.div n d` and `Usize.rem (n d : Usize) := UScalar.rem n d` are exact type specialization aliases; their equality to the selected existing operations is definitional (`rfl`), preserving the existing `Result` and error behavior. The lead reports a focused compile of this bridge already green.

## Import cache boundary

The cached Aeneas library directory used by the focused Lean runner is `.../aeneas-full/backends/lean/.lake/build/lib/lean`. It has no `Aeneas.olean`, `Aeneas/Data.olean`, or `Aeneas/Tactic.olean`. It does have `Aeneas/Std.olean`, `Aeneas/Tactic/RustAttributes.olean`, and `Aeneas/Data/Discriminant.olean`.

The pinned root import `Aeneas.lean` imports Command, Data, Do, Extract, Std, and Tactic. Its Data aggregator directly imports Array, BitVec, Byte, Discriminant, Fin, Int, List, Nat, Range, Tuples, Vector; `Data/Array.olean` and `Data/Vector.olean` are absent from the cache. Its Tactic aggregator directly imports Conv, Elab, Misc, RustAttributes, Setup, Simp, Simproc, Solver, Step, Tests; Setup/Simp/Simproc/Solver/Step/Tests aggregate oleans are absent. This explains why compiling `import Aeneas` is blocked with this cache.

A prior checked import-only pattern in canonical generated modules is available: `AspisR388ReduceU62/Funs.lean` and `AspisR403InterpolateThreeLimb/Funs.lean` use `import Aeneas.Std` and `import Aeneas.Tactic.RustAttributes`; corresponding Types modules additionally use `import Aeneas.Data.Discriminant`. All three selected modules are present in the cache. The lead has already chosen this focused import adapter; this note does not claim imports alone prove the selected functions.
