# R125: circle-source observer and ideal OOD wrapper

Source base: `e142da8c4caa973a925c822cdb3fee965c217cf5`.

Two focused Lean leaves now put the complete observed secure-circle sampler
behind the same arbitrary-history/freshness interface as q22 and prove the
corresponding ideal value-level OOD retry law. The actual source acceptance
predicate is proved equivalent to `parameter.im != 0`; this uses the source's
singular-first check order and the theorem that a nonzero imaginary component
forces the rational-map denominator to be nonzero.

## Exact proved boundary

- `SamplerObservedCircleHistoryLaw.observe_program` preserves the arbitrary
  visible prefix and identifies the observed source suffix with the complete
  bounded sampler program, including all retries, errors and the returned
  transcript state.
- `cached_oracle_history_law` keeps arbitrary prior memoized answers. Its
  independent-answer corollary requires the explicit branch-wise `FreshFrom`
  premise; no cache hit is resampled.
- `OODParameterRetryLaw` proves that three ideal uniform QM31 attempts fail
  with exact probability `((P^2)^3)/((P^4)^3)` and give equal probability to
  every accepted parameter with nonzero imaginary component.
- `source_accept_iff` proves that the actual circle policy accepts exactly the
  same `im != 0` parameters used by that ideal law.

This still does not prove that the actual eight-retry byte sampler induces the
ideal QM31 attempt law. The live callback prefix, shared memo table and visible
failure events also remain to be composed.

No hiding assumption, verifier path, field, query count, commitment, digest,
wire format, canonicality check, authentication check or rejection rule
changed.

## Resource-safe replay

A first broad simplification of the complete bounded recurrence reached
maximum recursion depth at 3,695,584 KiB RSS. It was replaced with named
`program_exact` and `observe_program` lemmas and was not retried with a higher
limit. The final two-target replay used Lean 4.32.0, `-j1 -M4500`, a 5/7 GiB
zero-swap cgroup and 629 pinned local/runtime dependencies.

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `OODParameterRetryLaw` | 0 | 1.60 s | 3,298,416 KiB | 0 |
| `SamplerObservedCircleHistoryLaw` | 0 | 1.76 s | 3,709,596 KiB | 0 |

Ten `#print axioms` audits contain no `sorryAx`. Three observer theorems inherit
the pinned Aeneas runtime's opaque `core.fmt.Formatter`; all other listed
dependencies are `propext`, `Classical.choice` and `Quot.sound`.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r125_evidence.py
```

No unchanged SBF suite was rerun. The measured verifier endpoint remains
**999,790 / 999,532 CU under the actual 1,000,000-CU cap** on the two genuine
fixtures, with only 210 CU margin on the larger run.

## First remaining proposition

Prove the source-to-ideal distribution theorem for one actual secure-circle
draw: four eight-retry limbs, outer rejection/continuation, shared-oracle state
advances and visible inner/outer exhaustion must induce the ideal QM31 attempt
law on fresh byte answers. Then compose the callback prefix's freshness or
explicit cache-hit loss.

Universal actual-source joint C1/H1/G compatibility including `p0/p2`, the
causal posterior simulator, seed/C2/eight-way commitment composition,
retry/publication accounting and coherent pre-beta quotient-pair extraction
remain open. Full privacy and full soundness are not proved.
