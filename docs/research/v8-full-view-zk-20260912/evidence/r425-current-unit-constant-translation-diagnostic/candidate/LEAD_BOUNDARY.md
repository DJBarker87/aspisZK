# R425 narrow unit constant evaluation candidate

Uncompiled draft. The helper accepts only the native Charon unit constant: `CAdt (None, [])` and type exactly `mk_unit_ty`. It returns the same zero-field runtime tuple used by `eval_rvalue_aggregate` on an empty tuple. No field operand is evaluated, no loan/borrow/symbolic identifier is allocated, and the evaluator returns the original context and identity continuation. All other unhandled constants retain the existing diagnostic failure. Existing literal, trait constant, const generic, function, raw-memory, and opaque cases are untouched.

This repairs an unsupported representation; it is not a universal compiler-preservation theorem or actual callback execution theorem. Focused native fixtures must include malformed unit encodings and the exact native-decoded recorded R419 input. The complete callback's state, failures, mutable gamma power, inverse, and publication chronology remain obligations after extraction.

The original R396 and R419 inputs contain the identical pointer-metadata unit constant in function58. Pinned Charon `ExpressionsUtils.mk_unit_const` defines precisely this shape. Pinned Aeneas `InterpExpressions.eval_rvalue_aggregate` constructs runtime `VAdt {variant_id=None; fields=[]}` and empty tuple type for zero operands. Saved source/API inventory provides the exact hashes and excerpts.
