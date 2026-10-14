# Exact inverse and image test for the released GRS polynomial

The checked algebraic specification now converts a polynomial in the
released circle-code image back to its 1024-coordinate message. Re-encoding
the result gives an exact image-membership test. This removes the need to
search all messages merely to recognize the circle subcode after an ambient
Reed–Solomon decoder returns a polynomial.

The definitions remain noncomputable Lean specifications, including the
existing matrix inverse. They are explicit finite algebraic formulas, not
an executable decoder or a proved runtime bound. The
[computability review](GRS-INVERSE-COMPUTABILITY.md) identifies the fixed
512-by-512 matrix dependency and confirms that these formulas do not search
the whole message space.

## Reused transformations

The old conversion writes the numerator as

```text
expand₂(L₅₁₂(p₀)) + 2X * expand₂(L₅₁₁(p₁)),
```

where both message polynomials have degree at most 511. The new inverse
composes four operations:

1. Extract even coefficients and half the odd coefficients, using the old
   parity lemmas. These recover the two fractional lifts exactly.
2. Apply `2^(-d) * L_d` at degrees 512 and 511. The new
   `fractionalLift_involution` proves `L_d(L_d(p)) = 2^d * p` under the
   displayed degree and field-cardinality assumptions. It reuses the old
   scalar involution, degree bound, and evaluation identities; no concrete
   512-term sum is expanded in its proof.
3. Reuse `monomialToNatural`, the existing inverse change-of-basis matrix,
   to recover each 512-coordinate natural-basis vector. The old matrix
   inverse identity proves this step. For arbitrary input polynomials it
   recovers the truncation; the original message's degree bounds justify
   removing that truncation.
4. Interleave those two vectors to recover the initial message. The old
   polynomial-pair injectivity theorem proves uniqueness.

`CircleNumeratorInverse.decoded_circleNumerator` proves the resulting
left-inverse law. `GRSMessageInverse.inverse_messagePolynomial` transports
it through the existing exact GRS conversion identity. No new assumption
about the ambient polynomial being an arbitrary valid circle message is
introduced.

## Exact image test

For any polynomial `q`, compute `m = inverse(q)` and compare the released
message polynomial of `m` with `q`.
`GRSMessageInverse.messagePolynomial_inverse_iff` proves:

```text
messagePolynomial(inverse(q)) = q
    iff there exists m with messagePolynomial(m) = q.
```

This is an exact test for the 1024-dimensional subcode within the ambient
degree-at-most-1024 polynomial space. It also rejects polynomials outside
that image. The theorem applies to arbitrary `q`; it does not assume image
membership as an input.

## Remaining decoder work and evidence

The [incremental merge](INCREMENTAL-CANDIDATE-MERGE.md) already proves exact
joint-list recovery from complete per-lane lists with bounded intermediate
family sizes. The [GRS route](GS-DECODER-REUSE-PATH.md) still needs executable
interpolation/root finding, refinement of the finite algebraic inverse and
merge representations, and a justified complexity argument. In particular,
the randomized finite-field factorization route cannot be substituted for
an unproved deterministic bit-complexity assertion.

The source base is `496110fcb2202fc8094191241f067a972071d396`. Focused NUC
receipts and the combined `LiftSubfieldCheckpoint` are archived in
`evidence/lean-lift-subfield-20261014/`. The combined checkpoint exited 0
in 1.16 seconds, at 2,866,220 KiB peak RSS with zero swap under 4G/6G/zero-swap
limits; all 21 axiom reports are standard-only. These results do not establish the
concrete causal classifier, Rust/source correspondence, or privacy.
