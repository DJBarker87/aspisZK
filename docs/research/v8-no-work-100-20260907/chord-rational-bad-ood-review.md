# Wrong batched OOD: at most three exact cleared folds

[ChordRationalBadOOD.lean](experiments/ChordRationalBadOOD.lean) now composes
the polynomial divisibility construction with the actual natural/radial OOD
interface. For a fixed natural original message `U`, a fixed checked OOD data
record, both OOD circle equations, and a nonzero chord-norm polynomial, it
proves:

> If either gamma-batched OOD answer is wrong for `U`, at most three alpha
> values in any finite challenge domain have zero cleared discrepancy.

The supplied final polynomial is an arbitrary function of alpha. There is no
final-degree, image, candidate-membership, provider-success, or quotient
recovery premise. The raw numerator is not an arbitrary asserted polynomial:
the theorem uses exactly `ChordRationalOOD.radialLanes (U-d.interpolant)`.

## Why this is a joint algebraic restriction

`four_exact_batched_correct` feeds four different exact cleared-fold equations
to `ChordRationalDivisibility.four_exact_folds_construct_polynomial_quotient`.
That theorem constructs a polynomial quotient. The new
`ChordRationalOOD.reconstructed_batched_ood` then evaluates the constructed
product identity at the two OOD chord zeros and proves both batches correct.

`wrong_batched_ood_exact_challenges_le_three` selects four distinct challenges
internally if its exact-discrepancy set supposedly has cardinality at least
four, and obtains a contradiction. This does not require the same final at
the four challenges. All raw-message, chord and OOD-answer inputs are fixed
across them.

The theorem is about exact **polynomial** cleared discrepancy, not an
assumption that a few sampled evaluations determine that polynomial. The
source-shaped numerator/fold representation and the separate degree-257
root bound are the next ingredients for partial query agreement. No norm
evaluation is divided out at the OOD points.

## Applicability and exclusions

- This is the exact-original-polynomial raw-word class. An arbitrary received
  helper word is not silently represented by a message `U`.
- Wrong **batched** OOD is required. A wrong component answer may cancel at
  gamma; its separately charged degree-28 component error remains relevant.
- Uniform conditional alpha sampling would turn the cardinality statement
  into a `3 / |challenge domain|` ideal contribution. This leaf does not prove
  that sampling/source/Fiat–Shamir law or attach that term to all acceptance.
- The nonzero norm is a polynomial premise. It does not require norm values
  at the OOD points or throughout the stored domain to be nonzero.
- A rational polynomial quotient and the totalized received-word division
  can differ at poles. The theorem makes no assertion of global equality to
  that totalized word and does not invoke the global exact-fold decoder on
  pole fibres.
- There is no payment-witness extractor, image-membership endpoint, global
  error certificate, full-view privacy result or CU claim here.

## Evidence

Run once:

```
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_rational_bad_ood.sh \
  docs/research/v8-no-work-100-20260907/experiments/chord-rational-bad-ood-v1.log
```

[Log](experiments/chord-rational-bad-ood-v1.log): exit 0; Lean 4.32.0; 22.61
seconds wall time; 5,590,138,880 bytes maximum RSS; zero swaps; both audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The
focused job used `-M7000` and the serialized aggregate 7-GiB guard, with no
dependency rebuild or unchanged leaf replay.

Research pin: `edb199c12fcc41f00330298b95b4736f60ac6f3a`; borrowed formal-source
closure pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The runner checks and
logs all source/olean pairs transitively before and after the run, with
explicit hashes for the newly proved chord dependencies. Concurrent main
was `db7a1847b4197a03e7772ca68132ce8fb2d861bf`; it was not modified.

- Source: `44de86a863db55db66b9c07407983f885bea29bf030ee28fce51591668418199`.
- Olean: `2947ecbe6dac311c8a33dd9121726682d716605ac0a70b0ce539d2e5dcff8dc7`.
- Runner: `1a8d880082f7e76d78fec6551d2a963b3952e30229f62d4bcf0d673f7105ba2f`.

Only new research proof/report artifacts were added. The proof-body model
remains 40,282 bytes; no runtime source or protocol message changed.
