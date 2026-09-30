# R132 verified evidence: uniform-state mean and fixed-tape circle/pair

Date: 2026-09-30 (UTC)

## Verified targets

Three focused leaves compiled successfully under the pinned 5G/7G,
zero-swap runner:

* `AspisV8R19/UniformStateFirstHitMean`: exit 0, wall 1.46 s, peak RSS
  3222960 KiB, swap 0.
* `AspisV8R19/IndependentMeanFixedTapeCircle`: exit 0, wall 1.88 s, peak RSS
  3717812 KiB, swap 0.
* `AspisV8R19/CirclePairRawFixedTapeLaw`: exit 0, wall 1.70 s, peak RSS
  3718272 KiB, swap 0.

All three report the recorded axiom set `propext, Classical.choice,
Quot.sound`.

## Exact uniform-state result

`mean_bad_indicator_eq_fraction (reads)` proves
`mean (badIndicator reads) = uniformBadFraction reads`; and
`mean_bad_indicator_bound (reads)` proves
`mean (badIndicator reads) ≤ (reads.length : ℚ) / (256 ^ 32 : ℚ)`.
These remain one-step statements for a fixed prior read list and a uniform
`State`.

## Conditional circle/pair boundary

The fixed-tape circle/pair theorem preserves the explicit branch-wise
`FreshFrom` premise inherited from the cached-history law, complete error,
result, state, history, and unused suffix views.  It is a deterministic
fixed-tape/representation composition under that premise.

This packet does not claim source-state uniformity, actual callback/shared
oracle equivalence, sampler distribution, privacy, or soundness, and does not
close the full sampler/source law.
