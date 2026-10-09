# R500 full declaration-table PrePasses diagnosis

This is a read-only replay of the **matching conditions** from pinned
`PrePasses.r491-candidate.ml`, applied to every structured function in the
unchanged R500 LLBC. It does not run Aeneas, alter the source, or assert a
source-semantics result.

## Pins and traversal

The exact input is `R499SplitAtPreconditionSelection.llbc`, SHA-256
`aa06813bc1d0d30cd2f286174e4f2767ecb9625b6aee3aa6f678d723b6f107fd`.
The matcher source is `PrePasses.r491-candidate.ml`, SHA-256
`587ab22f412f7344aa616cbda35d47bcdaf51492e7e79caaf0ab3bc4279a7eee`.

`apply_passes` at source lines 3678--3694 uses
`FunDeclId.Map.map` over `crate.fun_decls`, rather than `ordered_decls`.
The R500 input has 47 function-table slots, 43 populated and four already null
(IDs 28--31). `ordered_decls` has only Fun32, Fun33, and Types15/16/17; it
does not limit that map.

The only `slice_len_fn` is Fun1, concrete
`core::slice::{[u8]}::len<u8>`, with one erased region, no type parameters,
and expanded signature `&shared [u8] -> usize`. Its no-type-parameter matcher
branch accepts only candidate element type `u8`.

## Every direct metadata/Len match

There are no `Len`-form matches. The direct `Use PtrMetadata` matches, in
function-ID map order, are:

| function ID / instantiated source function | statement ID | element type | source span | result against concrete Fun1 |
| --- | ---: | --- | --- | --- |
| 2 `core::slice::<impl>::align_to::<u8,u32>` | 847 | `u8` | `core/src/slice/mod.rs:4513:20-4513:30` | accepted |
| 2 `core::slice::<impl>::align_to::<u8,u32>` | 934 | `u8` | `core/src/slice/mod.rs:4530:53-4530:63` | accepted |
| 4 `core::slice::<impl>::chunks_exact::<u8>` | 1016 | `u8` | `core/src/slice/iter.rs:1850:18-1850:29` | accepted |
| 4 `core::slice::<impl>::chunks_exact::<u8>` | 1062 | `u8` | generated `core/src/str/mod.rs:154:8-154:29` | accepted |
| **8 `core::slice::<impl>::chunks_exact::<u32>`** | **1083** | **`u32`** | **`core/src/slice/iter.rs:1850:18-1850:29`** | **unsupported: Fun1 input element is `u8`, while the no-type-parameter branch requires equality** |
| 8 `core::slice::<impl>::chunks_exact::<u32>` | 1129 | `u8` | generated `core/src/str/mod.rs:154:8-154:29` | would be accepted, but follows the failure above |
| 10 `core::slice::iter::<impl Iterator>::next::<u32>` | 1154 | `u32` | `core/src/slice/iter.rs:2155:18-2155:28` | unsupported if reached |
| 20 `core::slice::<impl>::align_to_offsets::<u8,u32>` | 1381 | `u8` | `core/src/slice/mod.rs:4465:21-4465:31` | accepted if reached |
| 22 `core::slice::<impl>::split_at_unchecked::<u8>` | 1408 | `u8` | `core/src/slice/mod.rs:2044:18-2044:28` | accepted if reached |
| 23 `core::slice::<impl>::split_at_unchecked::<u32>` | 1503 | `u32` | `core/src/slice/mod.rs:2044:18-2044:28` | unsupported if reached |
| 25 `core::num::<impl usize>::unchecked_sub::precondition_check` | 1632 | `u8` | generated `core/src/str/mod.rs:154:8-154:29` | accepted if reached |
| 32 `core::slice::<impl>::split_at_unchecked::precondition_check` | 1854 | `u8` | generated `core/src/str/mod.rs:154:8-154:29` | accepted if reached |

The first failing callback in map-key order is therefore Fun8 statement1083:
its reference expands to `&shared [u32]`, so `slice_len_type_args u32` takes
neither the generic branch nor Fun1's equality branch and raises the recorded
failure. Fun8 is not an `ordered_decls` member or a selected dependency row.
This verifies the stated U32-iterator suspicion as an AST/matcher fact.

## Raw-pointer definition matches

The initial `metadata_definition` pattern also matches five definitions:
Fun2 statements832,902,929 (`u8`); Fun22 statement1410 (`u8`); and Fun23
statement1505 (`u32`). Those require the separate single-definition/single-
metadata-read classifier after the direct rewrite. They are recorded in
`FULL_FUNCTION_METADATA_CANDIDATES.json`; none precedes direct Fun8/1083 as an
unsupported element-type invocation. No claim is made here about their final
classifier outcome.

## Projection-slot observation only

The format already uses null `fun_decls` slots (28--31), so a future projection
can represent omission by nulling function-table entries without changing the
remaining IDs. The existing selection manifest proves only that the current
R499 projection preserved every table entry and changed `ordered_decls`.

Mechanically, retaining Fun32 and its complete recorded dependency rows retains
Fun33 and Types15/16/17. Retaining Fun1 is additionally required by the
prepass's global `slice_len_fn` lookup, although Fun1 is absent from the
five-row ordered closure. Thus a proposed null-slot projection would need to
retain at least function slots 1, 32, and 33 plus those type rows, and null
only entries outside that retained set. This is a representation and dependency
inventory, not an implemented projection or a claim that a modified LLBC will
translate.
