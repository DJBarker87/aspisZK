# OOD word bridge and corrected semantic endpoint

This continuation establishes two deterministic facts and rejects one invalid
source-correspondence target.

## Four-block word representation

`FSV7FourBlockWordBridge.lean` proves that the current transcript's
little-endian `words` for four chronological 32-byte blocks are exactly the
V7 `flattenedWords` / `fourGammaBlocksRawEquiv` stream after the source's
31-bit mask.  This permits reuse of the existing V7 eight-retry sampler law at
the representation boundary.

It does not construct the variable one-to-four block window consumed by the
actual current `challenge`, nor prove its blocks fresh.  The remaining bridge
must retain cache hits, unused words and every rejection path.

## Semantic endpoint correction

`SourcePolynomialEndpointObstruction.lean` proves that the selected Rust
semantic callback cannot generally equal `tableMLEValue` of its Boolean
restriction.  The source contains degree-greater-than-one constraint factors;
the minimal Booleanity example `x0 * (x0 - 1)` is zero on every Boolean row
but can be nonzero at an off-domain point.  Hence the earlier canonical-table
reference trace is not the actual source-polynomial trace.

The retained positive theorem proves the exact linear masking identity.  The
correct next endpoint is a reference trace built from partial Boolean sums of
the actual degree-27 source polynomial, with endpoint `payment_terminal`, plus
a separate refinement of the Rust mask evaluator.  No global probability term
is changed by this correction.

## Post-OOD gamma source slice

`FSV8PostOODGammaScript.lean` constructs one causal script containing the
successful OOD body, the literal label-28 eight-byte nonce absorption, and the
three-attempt nonzero-QM31 gamma sampler.  From one successful composed run it
recovers the exact successful OOD prefix and gamma run and proves gamma is
nonzero.  Failed OOD or gamma paths remain abort/error results.

All three focused leaves were checked with pinned Lean 4.32.0 on the bounded
NUC runner.  Machine evidence is stored under the corresponding results
directories.  These are deterministic/source-interface results, not a
complete random-oracle sampler theorem or global soundness result.
