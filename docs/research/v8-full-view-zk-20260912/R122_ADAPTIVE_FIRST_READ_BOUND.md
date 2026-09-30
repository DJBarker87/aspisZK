# R122: adaptive first-read law and fixed-root exceptional bound

Source base: `3c06e2ac4a622701a67195fa5923b8a609eac0b9`.

The shared-oracle conditioning gap is now split into two exact, compiled
pieces. First, a generic causal program whose every reached address is a first
read has exactly the same law as a program receiving a fresh independent
uniform answer at each query. The next address and stopping time may depend on
all earlier answers. Second, for every permitted fixed tuple of 22 distinct
query roots excluding one, the two-swap residual determinant is singular on at
most

\[
\frac{819}{(2^{31}-1)^4}
\]

of product-uniform QM31 challenge assignments (approximately `2^-114.3`).

This does **not** yet apply that number to the source protocol. The first-read
premise for the honest challenge-generation segment relative to its existing
cache, or a bound on its failure, remains open. The complete prover/verifier
experiment intentionally contains later cached verifier replays; those stay in
the memoized semantics and must never be resampled. The accepted source
samplers must then be connected to the product-uniform challenge tuple while
retaining failures, retries and publication.
No future q22 root is conditioned on in either new theorem.

## Exact proved boundary

- `AdaptiveFirstReadLaw.FreshFrom` is a branch-wise predicate over the existing
  memoized causal `Program`. At each reached query its address must be absent
  from the current table; the returned answer is inserted before recursion.
- `lazyMean_eq_independentMean` proves exact equality between the memoized
  interpreter and sequential independent uniform answers under `FreshFrom`.
  It allows adaptive addresses, answer-dependent control flow and variable
  stopping. Cache hits are not resampled; they violate the premise.
- `complete_oracle_eq_independentMean` and
  `empty_oracle_eq_independentMean` connect that law to the existing complete
  finite-oracle semantics. `independentMean_bind` supplies exact sequential
  composition rather than an informal independence assertion.
- `TwoSwapFixedRootProbability` instantiates Mathlib's multivariate
  Schwartz--Zippel theorem with R121's source-shaped two-swap determinant,
  its nonzero certificate and total-degree bound 819.
- The exact tower cardinalities are proved in Lean:
  `|CM31|=(2^31-1)^2` and `|QM31|=(2^31-1)^4`. The stated bound is therefore an
  exact finite-set fraction, not a floating-point estimate.

The polynomial continues to include all three point observations and all seven
relation coefficients for each channel from R121. This result does not add a
hiding assumption, alter the verifier, or weaken decoding, authentication,
query count, digest width or rejection behavior.

## Reproducible evidence

The final frozen replay compiles two changed leaves against the R121 cache:

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `AdaptiveFirstReadLaw` | 0 | 1.57 s | 3,238,132 KiB | 0 |
| `TwoSwapFixedRootProbability` | 0 | 1.46 s | 2,474,352 KiB | 0 |

There are 11 `#print axioms` audits. They report only `propext`,
`Classical.choice` and `Quot.sound`; the primitive two-query freshness
equivalence is axiom-free. The replay uses Lean 4.32.0, `-j1 -M4500`, a 5/7
GiB zero-swap cgroup and 272 pinned dependencies. Exact commands, source
hashes and logs are in [the evidence directory](evidence/r122-adaptive-first-read/receipt.json).

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r122_evidence.py
```

No verifier source changed and no unchanged SBF suite was rerun. The measured
endpoint remains **999,790 / 999,532 CU under the actual 1M cap** on the two
genuine fixtures, with only 210 CU margin on the larger run.

## First remaining proposition

Compile the honest source challenge-generation segment into the causal
oracle-program interface and prove `FreshFrom` relative to its prior cache, or
bound the probability that one of its designated squeeze/advance addresses was
already read. Keep the complete prover/verifier experiment in the memoized
semantics so intentional verifier replays remain cache hits. Then bind the
already proved accepted QM31/q22 observer semantics to the independent-answer
interpreter so the fixed-root `819/(2^31-1)^4` determinant bound applies to the
actual accepted prefix without conditioning on future roots.

This still does not close universal joint C1/H1/G affine-image compatibility,
the causal posterior simulator, seed/C2/eight-way commitment composition,
retry/publication behavior, or coherent pre-beta quotient-pair extraction and
soundness loss accounting. Full privacy and full soundness remain unproved.
