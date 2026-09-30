# R123: source-domain determinant bound and one-step first-read loss

Source base: `3adf97234b5cd67f8d7eb69b82a7248b98956561`.

Six focused Lean leaves now connect R122 to the byte-framed source primitives
and to the exact finite domains used by the fixed-root two-swap determinant.
For one source squeeze after a concrete prior trace, freshness of both framed
oracle addresses implies the independent-answer law. Otherwise the current
32-byte state lies in an explicit bad-state set whose independently uniform
fraction is at most the number of prior read addresses divided by `256^32`.

The algebraic side now uses coordinate-specific domains. With
`P = 2^31 - 1`, Lean proves:

- full QM31: `P^4` values;
- nonzero QM31: `P^4 - 1` values;
- accepted OOD parameter (`im != 0`): `P^2 * (P^2 - 1)` values.

For fixed valid q22 roots, the determinant-zero fraction over the resulting
product grid is at most `819 / (P^2 * (P^2 - 1))`. Requiring the two OOD
parameters to differ is represented by an explicit admitted subset, is proved
nonempty, and retains the exact acceptance-ratio divisor. That ratio is not
silently discarded or yet simplified into a source probability.

This is not a complete source-sampler theorem. The selected verifier is the
explicit research callback, whose second OOD point has a three-attempt
distinctness wrapper. Production V6 samples its two OOD points independently.
R123 does not transfer the research wrapper rule to production V6.

## Exact proved boundary

- `AdaptiveFirstReadSource.traceCache` reconstructs the memo table from the
  complete prior query/answer trace. `traceCache_missing_iff` characterizes a
  missing cell without importing the unavailable older `runQueries` model.
- `squeezeProgram_fresh_after_trace` turns the byte-level source `Fresh`
  predicate into R122's branch-wise `FreshFrom` premise for one actual
  squeeze/advance pair. `fresh_squeeze_lazy_law` then applies the exact
  independent-answer reduction.
- `AdaptiveFirstReadLoss.fresh_or_bad_state` is a pathwise dichotomy. Its
  counting theorem only concerns an independently uniform current state; it
  is not a whole-run union bound or a claim that the source state is uniform.
- `TwoSwapDomainProbability.schwartz_zippel_min_card` proves the
  coordinate-specific finite-grid bound with no extra factor for 36
  variables.
- `TwoSwapSourceDomains` binds coordinates 0--9 to full QM31, coordinate 10
  to nonzero QM31, coordinate 11 to full QM31 and coordinates 12--13 to the
  OOD domain. In the fixed-root determinant, coordinates 14--35 are syntactic
  remnants after substituting the 22 roots; their assigned full domains do not
  claim another source draw.
- `TwoSwapDistinctRestriction` preserves the exact admitted-set density in
  the denominator. `TwoSwapSourceDistinct` supplies an explicit legal pair of
  distinct OOD parameters and instantiates that theorem on the source domain.

No hiding assumption, verifier path, field, query count, commitment, digest,
wire format, canonicality check, authentication check or rejection rule
changed.

## Resource-safe proof repair

Three early cardinality proofs tried to normalize subtype complements. They
hit Lean's `-M4500` kernel memory limit at approximately 4.61 GiB RSS (and one
also hit maximum recursion depth). They were not retried with a larger cap.
The replacement proves the same result structurally: `Set.card_ne_eq` handles
nonzero values, while an explicit equivalence identifies OOD QM31 values with
`CM31 x nonzero CM31`. The final source-domain leaf compiles in 1.51 seconds
at 2,465,472 KiB RSS. The retained failure record is in
`evidence/r123-source-domain-bound/failed-formulations.json`.

## Reproducible evidence

All six changed leaves were replayed once against the R122 cache with Lean
4.32.0, `-j1 -M4500`, a 5/7 GiB zero-swap cgroup and 272 pinned dependencies.
The exact common command, source/output roots and expanded target list are in
`evidence/r123-source-domain-bound/command.json`.

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `AdaptiveFirstReadSource` | 0 | 1.70 s | 3,238,464 KiB | 0 |
| `AdaptiveFirstReadLoss` | 0 | 1.52 s | 3,230,148 KiB | 0 |
| `TwoSwapDomainProbability` | 0 | 1.51 s | 2,463,104 KiB | 0 |
| `TwoSwapSourceDomains` | 0 | 1.51 s | 2,465,472 KiB | 0 |
| `TwoSwapDistinctRestriction` | 0 | 1.40 s | 2,454,764 KiB | 0 |
| `TwoSwapSourceDistinct` | 0 | 2.74 s | 2,483,892 KiB | 0 |

There are 17 `#print axioms` audits. They use only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` appears.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r123_evidence.py
```

No unchanged SBF suite was rerun. The measured verifier endpoint remains
**999,790 / 999,532 CU under the actual 1,000,000-CU cap** on the two genuine
fixtures, with only 210 CU margin on the larger run.

## First remaining proposition

Compose the pinned research callback's complete pre-query transcript state,
observed history and memo table with the already proved ordinary QM31,
nonzero-QM31, OOD and q22 operational models. Prove the law of the callback's
three-attempt distinct-second-point wrapper, including its visible failure
probability, and lift `QueryObservedProgram.cached_oracle_law` from empty
history to that fixed prefix. Intentional cache hits remain memoized.

Even after that, universal joint C1/H1/G affine-image compatibility (including
`p0/p2`), the causal posterior simulator, seed/C2/eight-way commitment
composition, retry/publication accounting and coherent pre-beta quotient-pair
extraction remain open. Full privacy and full soundness are not proved.
