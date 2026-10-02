# R346 after-guards callback suffix raw staging

This is uncompiled scratch staging from frozen R292 `Funs.input.lean` (SHA-256 `4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4`). The builder checks the copied source and the original frozen provenance input, then extracts the exact contiguous block at original lines 527–605 inclusive. `selected-source-fragment.txt` preserves those source lines verbatim, including the final `ok (core.result.Result.Ok (ox2, oy2))`. The Lean wrapper passes `xs` and `ys` only and keeps the source operations unchanged.

The selected block begins inside the `else` branch after the source has checked `xs` and `ys` nonempty and run the chained iterator predicate; it excludes those checks and the `b2` branch that returns `Error.Domain`. This wrapper makes no full-callback guard or whole-source claim. The block itself retains the existing prefix, field, last/unwrap, `from_elem`, reverse-loop, and index-zero write calls.

The inner `core.result.Result` error parameter requires care. R292's generated `AspisR292PrivateBatch.Error` comes from `R292Types.input.lean`; it records the same source span and seven constructors as the existing `AspisR156FullFreeze.Error`. The wrapper uses the latter available source model, and the audit records that these are distinct Lean declarations, not definitionally identical. The selected suffix only constructs `core.result.Result.Ok`; it never constructs an inner error. This is an unresolved binding for lead review, not an asserted equivalence or an error-type substitution claim.

`#print axioms selectedAfterGuards` is present. No Lean compile or axioms output was run. Nested source/build hashes are preserved in `SHA256SUMS`.
