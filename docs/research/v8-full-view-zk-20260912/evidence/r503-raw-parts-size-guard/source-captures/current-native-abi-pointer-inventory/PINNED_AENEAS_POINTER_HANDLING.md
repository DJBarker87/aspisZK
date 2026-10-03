# Pinned Aeneas pointer-operation source inventory

Read-only inventory; no compilation, source edits, new capture, or semantics proposal.

## Exact relationship to the R497 binary

The current binary under discussion is R497 candidate SHA-256 `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`, built from Aeneas base revision `56a931fc3879354a2fa584e73bd0a1d412714851` plus scoped source changes. Its exact workspace is `/home/dombarker/project-offloads/aspis-r490-slice-len-concrete-20261003-a/src`.

I verified the current workspace hashes read-only over SSH. The relevant interpreter files are byte-identical to the saved R437 files: `interp/InterpExpressions.ml` SHA `a686db5af43c4463b357e066330a21f01287bafe0cc2c13394b4b2b4f458f190`; `interp/InterpStatements.ml` SHA `061c0b53ee02aa2b19ab2998ad84a7a5e3f3add06f66deaec839f8dff7343982`; `interp/InterpPaths.ml` SHA `d72a6ec2a45bc738fab3e5c666e552dc0f28c031ddcba5a9f46a05415c3cf10e`. Therefore those dispatch findings below apply to the R497 source candidate by exact file identity.

`PrePasses.ml` is **not** byte-identical to the R437 copy: R497's R491 candidate is SHA `587ab22f412f7344aa616cbda35d47bcdaf51492e7e79caaf0ab3bc4279a7eee`; base was `579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17`. Its scoped difference in the metadata-only pass is generic argument selection for `slice_len_fn`: it checks the declared type-parameter arity/signature and fails closed for unsupported forms. Candidate `ExtractBuiltinLean.ml` SHA `4982d10c816d2fb01546063dea11fdda92d2726373952f163200303ffa501a6f` adds one exact `core::slice::{[u8]}::len<u8> -> Slice.len` mapping. The R491 source and builtin mapping diffs are saved in `.r21-scratch/r497-slice-len-concrete/evidence/`. Neither change implements RawPtr, Offset, or PtrFromParts. The build receipt is `.r21-scratch/r497-slice-len-concrete/evidence/r497-slice-len-concrete-build/build-result.json`.

The Lean dependency source hashes were confirmed read-only on that host: `Aeneas/Std/RawPtr.lean` `752bb5fdf1b79c10262a1c7cc03d780b51e47ef0c473ac259c57408af6c82f47`; `Aeneas/Std/Slice.lean` `e3297bf6d38564e500ab798776624239134ae4d03eb704132a1d17eb6dff2d03`. The source type/model observations below therefore match the linked source files in that cached library.

## Provenance and source hashes

R437 inventory records Aeneas source revision `ee7ba72da456d5f353bca9f6739b23750a5dfffa` at `/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/src`; Lean library at `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean`. Full receipts are `.r21-scratch/r437-pointer-source-boundary/inventory/inventory.json` and `SHA256SUMS`.

Relevant exact file hashes from that receipt:

- `aeneas/PrePasses.ml` `579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17`
- `aeneas/InterpStatements.ml` `061c0b53ee02aa2b19ab2998ad84a7a5e3f3add06f66deaec839f8dff7343982`
- `aeneas/InterpExpressions.ml` `a686db5af43c4463b357e066330a21f01287bafe0cc2c13394b4b2b4f458f190`
- `aeneas/InterpPaths.ml` `d72a6ec2a45bc738fab3e5c666e552dc0f28c031ddcba5a9f46a05415c3cf10e`
- Charon `generated/Generated_Types.ml` `6e977831c8fb7a3e1b6b77e1b98e5cc71de8841186f98c5de5fd68c93fdb9794`
- Lean `Aeneas/Std/RawPtr.lean` `752bb5fdf1b79c10262a1c7cc03d780b51e47ef0c473ac259c57408af6c82f47`
- Lean `Aeneas/Std/Slice.lean` `e3297bf6d38564e500ab798776624239134ae4d03eb704132a1d17eb6dff2d03`

## IR types and pointer carrier

Charon's saved `Generated_Types.ml` lines 777, 804 defines LLBC types `TRawPtr of ty * ref_kind`, `TRef of region * ty * ref_kind`, and `TPtrMetadata of ty` (the last described as a marker for taking metadata out of a type). Its builtin function ID `PtrFromParts of ref_kind` is described as building a raw pointer from data pointer plus metadata (which may be unit for thin pointers), substituted for `AggregateKind::RawPtr` when `--ops-to-function-calls` is enabled.

The Lean library's `Aeneas.Std.RawPtr` does not encode an address: `structure RawPtr (T) (M) where v : T`; `Mutability` has `Mut | Const`. The source comment says “We don't really use raw pointers for now.” `RawPtr.cast_scalar` returns `Result (RawPtr T' M')` and its body is exactly `.fail .undef` (lines 29–31); this is not a successful pointer cast model. `Aeneas.Std.Slice` is list-backed (`Slice.length := v.val.length`); `Slice.len` returns `Usize.ofNatCore v.val.length` with a proof from the slice length bound (lines 35–55). These Lean types carry no allocation identity, address, provenance, or lifetime.

## Translation/interpreter cases

| Input operation | Existing pinned handling, exact source location | Guard / output / failure boundary |
|---|---|---|
| `RawPtr` rvalue | `InterpExpressions.ml` `eval_rvalue_not_global`, lines 1489–1518, dispatches `Use`, `RvRef`, unary/binary op, aggregate, discriminant, `Len`, then wildcard raises `Unsupported operation`. `RawPtr` is not a handled arm. `InterpStatements.ml` lines 922–962 only reaches assignment synthesis after this evaluation succeeds. | No raw-pointer construction result/guard is implemented in this evaluator. Independently, pointer dereference is rejected in `InterpPaths.ml:115` with “Aeneas does not yet support dereferencing raw pointers.” |
| `PtrMetadata` projection | `PrePasses.ml:90–115,122–222` has a *narrow* metadata-only slice-raw-pointer elimination pass. It recognizes a raw slice pointer created from a dereferenced **shared safe slice reference**, whose usize metadata is copied from that same reference. It rewrites direct metadata extraction of a shared slice ref to the unique `slice_len_fn` call. | The raw pointer temporary is rewritten only with exactly one definition and exactly one use, that use being a read of its usize metadata; any dereference, cast, comparison, address observation, call escape, reassignment, or second use invalidates the candidate. R495 Fun22/Fun23 later cast the raw pointer and use `Offset`, so the saved pass's stated filter does not cover that whole use pattern. No general PtrMetadata evaluator case is in saved `InterpPaths`/`InterpExpressions`/`InterpStatements` matches. |
| Raw-pointer cast | `InterpExpressions.ml:1005` recognizes `CastRawPtr` only to infer the target type in the cast-type selector; saved Lean `RawPtr.cast_scalar` is `.fail .undef`. | The type selector is not an evaluator semantics case. The shown Lean scalar cast fails with `.undef`; no source-side pointer identity/provenance result is established by these excerpts. |
| `BinaryOp::Offset` | `InterpExpressions.ml:1153–1211`: symbolic integer-operand type selection explicitly groups `Offset` with `AddChecked`, `SubChecked`, `MulChecked` and raises `Unimplemented binary operation` (`1193`). Concrete scalar evaluation at `1034–1140` has scalar arithmetic/comparison cases; `Offset` has no successful scalar arm. | If an Offset reaches concrete computation with non-scalar pointer inputs, it falls outside the scalar pair case and raises `Invalid inputs for binop`; it does not calculate a pointer. No offset-success/guard contract appears here. |
| `PtrFromParts Shared` builtin | `InterpStatements.ml:450–472`, builtin evaluator dispatch includes `PtrFromParts _` in the explicit “Unimplemented” case. | All `PtrFromParts` ref kinds hit that branch; there is no successful pointer reconstruction result or guard/error analysis beyond the interpreter's unimplemented failure. |

The generic assignment synthesis arm includes `RawPtr` (`InterpStatements.ml:937–962`), but that arm follows successful `eval_rvalue_not_global`; the latter wildcard rejects it. It does not supply raw-pointer semantics.

## Scope limit

These are source dispatch/type observations from the exact saved files above. They identify current implementation boundaries only. They do not define replacement operation semantics, prove a Rust memory model, justify any caller premise, or establish correspondence for R495. The prior R437 README and inventory explicitly warn against such inferences.
