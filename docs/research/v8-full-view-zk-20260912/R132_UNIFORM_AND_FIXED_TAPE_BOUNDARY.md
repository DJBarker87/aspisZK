# R132: uniform-state mean result and fixed-tape circle/pair boundary

Source base: `9f9913b08a129c662d365ce8ea25ac2352729509`.

The verified packet contains three focused compiled leaves.  The already compiled leaf
`AspisV8R19/UniformStateFirstHitMean` contributes exactly the following
one-step, uniform-state-only results for a fixed prior read list `reads`:

```text
mean (badIndicator reads) = uniformBadFraction reads
mean (badIndicator reads) ≤ reads.length / (256 ^ 32 : ℚ)
```

The source prints axioms for `mean_bad_indicator_eq_fraction` and
`mean_bad_indicator_bound`; this packet records the exact theorem statements,
not a whole-run source-state uniformity claim.

The fixed-tape circle/pair leaves `IndependentMeanFixedTapeCircle` and
`CirclePairRawFixedTapeLaw` also compiled successfully.  Their exact timing,
RSS, swap, and axiom records are in the machine-readable receipt and logs.

The circle/pair theorem remains conditional on its explicit branch-wise
`FreshFrom` premise; this is not a source callback or distribution theorem.

This packet makes no `FreshFrom`, source-callback equivalence, sampler
distribution, privacy, or soundness claim.  It does not close the full
sampler/source law.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r132_evidence.py
```
