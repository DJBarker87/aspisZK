# R500 PrePasses Fun32 slice-length diagnosis

Scope: a read-only inspection of FunDeclId 32 in the exact R500 input. This
records AST pattern matching only. It makes no source-correspondence or proof
claim and does not identify the function that raised the recorded translation
failure outside this scope.

## Pinned inputs

| input | SHA-256 |
| --- | --- |
| `../R499SplitAtPreconditionSelection.llbc` (same bytes as R500 saved input) | `aa06813bc1d0d30cd2f286174e4f2767ecb9625b6aee3aa6f678d723b6f107fd` |
| `../../r497-slice-len-concrete/evidence/PrePasses.r491-candidate.ml` | `587ab22f412f7344aa616cbda35d47bcdaf51492e7e79caaf0ab3bc4279a7eee` |

R500 recorded exit status 2 after 0.16 s, with 57,024 KiB peak RSS and zero
swap. Its recorded message is `Unsupported slice_len_fn generic/signature
shape in metadata rewrite` at `PrePasses.ml:198-199`.

The sole declaration whose `item_meta.lang_item` is `slice_len_fn` is FunDeclId
1, named `core::slice::{[u8]}::len<u8>`. Its generics are one erased region and
no type parameters. Its expanded signature is:

```
input:  &shared [u8]
output: usize
```

Therefore `slice_len_type_args` can return `[]` only where the candidate
`elem_ty` is exactly `u8` (the `generics.types = []` branch at lines 193--197).

## Fun32 candidates

FunDeclId 32 is `core::slice::<impl>::split_at_unchecked::precondition_check`;
its declared source span is `core/src/ub_checks.rs:68:12-68:55`.
The structured body has no `Len` assignment. It contains the following three
metadata/raw-pointer statements.

| statement id | AST statement / span | matched PrePasses route | expanded relevant types | result of that route |
| --- | --- | --- | --- | --- |
| 1843 | `Local13 := RawPtr(Deref Local4, Shared, Copy PtrMetadata(Local4))`; `core/src/fmt/mod.rs:815:4-823:5`, generated from `core/src/str/mod.rs:575:8-575:12` | `metadata_definition` is considered first | `Local4: &shared str`; dereference: `str`; `Local13: *const str`; metadata: `usize` | Does **not** match `metadata_definition`: its destination must be `RawPtr (TSlice raw_elem_ty, _)`, but this destination is `RawPtr(str, Shared)`. It does not reach `slice_len_call`. |
| 1844 | `Local8 := cast(Local13)`; same outer source span, generated from `core/src/str/mod.rs:575:8-575:39` | neither direct metadata nor raw-pointer definition pattern | `Local13: *const str`; `Local8: *const u8` | No `Len`, `PtrMetadata` use, or `RawPtr` RHS. It cannot call `slice_len_call`. |
| 1854 | `Local12 := Copy PtrMetadata(Local14)`; `core/src/fmt/mod.rs:815:4-823:5`, generated from `core/src/str/mod.rs:154:8-154:29` | `direct_metadata_rewriter` second arm | `Local14: &shared [u8]`; destination and metadata: `usize`; candidate `elem_ty = u8` | Matches. Fun1 input element type is also `u8`, so the empty-type-argument branch returns `[]`; this candidate has no element-type mismatch. |

The span paths within the structured body are:

```
1843: /Structured/body/statements/6/kind/Switch/If/2/statements/5
1844: /Structured/body/statements/6/kind/Switch/If/2/statements/6
1854: /Structured/body/statements/6/kind/Switch/If/2/statements/16
```

## Exact bounded finding

Within Fun32, the string-valued panic-formatting raw-pointer sequence is not a
`metadata_definition` candidate and cannot invoke `slice_len_call`; the only
candidate that invokes it has `u8` element type, equal to the concrete Fun1
signature's `u8`. This inspection therefore finds no `slice_len_call`
element-type/signature mismatch in Fun32. The recorded R500 failure remains
unattributed by this bounded inventory.
