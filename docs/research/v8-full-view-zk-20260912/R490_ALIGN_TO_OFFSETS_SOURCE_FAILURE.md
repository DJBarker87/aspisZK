# R490 actual `align_to_offsets` translation failure

The selected u8/u32 `align_to_offsets` LLBC was extracted in R488 capture d.
The subsequent R490 Aeneas invocation failed before producing a Lean proof or
generated Lean artifact. It exited 2 after importing the LLBC, with
`Invalid_argument "option is None"` in Aeneas function analysis at
`llbc/FunsAnalysis.ml:176` while visiting an rvalue.

The exact input, invocation, result metrics, extraction flags, compiler
constants, log references, and checksums are saved in
[`evidence/r490-align-offsets-source`](evidence/r490-align-offsets-source/README.md).
This evidence does not establish parser behavior, source correspondence,
alignment behavior, or any privacy or soundness property.

## Later literal-candidate status

R490 literal candidate f later translated the same selected LLBC successfully
with the concrete `u8` slice-length builtin registration. This generated
`Types.lean` and `Funs.lean`; it did not prove either one. The focused adapted
`Types.lean` target compiled. An initial focused adapted `Funs.lean` target
stopped on missing old-cache aliases `Aeneas.Std.Usize.div` and
`Aeneas.Std.Usize.rem`; the later focused Funs target compiled after importing
the R498 definitionally identical primitive-name compatibility module.

The concrete matcher repair is supported by a pinned runtime matcher probe and
binds only the captured `u8` primitive to the supplied `Slice.len` builtin.
It adds no new standard-library semantics or source assumption. The R484
binding evidence separately verifies the existing `UScalar` primitive name
identity. Those results alone did not prove `align_to_offsets`, the parser, or
source correspondence; the later R496 helper result is stated below.

## R496 generated-helper execution result

R496 now proves the actual generated `align_to_offsets::<u8,u32>` helper over
the supplied bounded Aeneas `Slice U8` representation. For every such slice,
the helper succeeds with quotient `len / 4` and remainder `len % 4`, proves
the quotient/remainder partition and `remainder < 4`, and rules out every
generated-helper error result. This is a proof of the generated helper's
execution only.

The next proposition remains the native `align_to` successful
prefix/words/suffix image and its connection to the ordered fields loop, Vec
length, canonical/error behavior, and caller frame. Those native and
whole-parser arguments remain open.
