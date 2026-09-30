# R124: observed q22 prefix and ideal distinct-retry law

Source base: `1d1c3137fea33d9481caf5616123f438539641dd`.

Four focused Lean leaves now retain an arbitrary visible history in the q22
observer law, reduce that law to sequential independent answers under one
explicit branch-wise freshness premise, and prove the ideal outer
three-attempt distinct-second-OOD distribution. A separate guarded oracle
program makes a memo-table collision return `none`; this gives an exact
fail-visible independent-answer law without resampling an already-used oracle
cell.

This does not yet identify the ideal model with the complete callback. The
pinned research callback's pre-q22 transcript/cache and the secure-circle
inner rejection sampler still need source composition. Production V6 does not
use the research callback's distinct-second-point wrapper.

## Exact proved boundary

- `QueryObservedHistoryLaw.cached_oracle_history_law` generalizes the existing
  q22 observer theorem from empty history to an arbitrary visible prefix. It
  deliberately leaves the history and memo table independent parameters.
- `QueryObservedFreshHistoryLaw.cached_oracle_history_eq_independentMean`
  composes that observer theorem with R122's adaptive first-read result. The
  only new premise is `FreshFrom challengeProgram t`; intentional cache hits
  are not silently resampled.
- `GuardedFirstRead.guardFresh` stops with a visible `none` before a cache hit.
  It is fresh by construction and agrees with ordinary option-lifted execution
  on fresh branches. No equivalence with the unguarded callback is claimed.
- `OODDistinctRetryLaw` works over the exact subtype
  `{z : QM31Exact // z.im != 0}`. For a fixed first point and three independent
  ideal attempts, Lean proves failure probability `1 / sourceMinimum^3`, equal
  probability for every accepted second point and accepted-domain cardinality
  `sourceMinimum - 1`.

The retry theorem excludes failures inside each secure-circle draw and does
not identify independent ideal tapes with the shared source oracle. Those are
the source-specific obligations that prevent promotion to a callback law.

No hiding assumption, verifier path, field, query count, commitment, digest,
wire format, canonicality check, authentication check or rejection rule
changed.

## Resource-safe proof repair

The first direct subtype/Finset cardinality formulation reached Lean's maximum
recursion depth at 2,447,808 KiB RSS. It was not retried by raising the kernel
limit. The replacement uses the existing secure-OOD product equivalence and
`Set.card_ne_eq`; the completed target compiles in 1.54 seconds at 2,451,112
KiB RSS. A separate initial q22 invocation used the Aeneas source directory
instead of its compiled object directory and was corrected without changing a
theorem. Both attempts are retained in
`evidence/r124-observed-retry-law/failed-formulations.json`.

## Reproducible evidence

All four changed leaves were replayed once against the R122 cache with Lean
4.32.0, `-j1 -M4500`, a 5/7 GiB zero-swap cgroup and 594 pinned local/runtime
dependencies.

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `GuardedFirstRead` | 0 | 1.86 s | 3,220,204 KiB | 0 |
| `QueryObservedHistoryLaw` | 0 | 2.12 s | 3,675,840 KiB | 0 |
| `OODDistinctRetryLaw` | 0 | 1.54 s | 2,451,112 KiB | 0 |
| `QueryObservedFreshHistoryLaw` | 0 | 2.09 s | 3,674,396 KiB | 0 |

There are nine `#print axioms` audits and no `sorryAx`. The two q22 observer
audits inherit `core.fmt.Formatter` from the already pinned Aeneas runtime; the
remaining dependencies are `propext`, `Classical.choice` and `Quot.sound`.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r124_evidence.py
```

No unchanged SBF suite was rerun. The measured verifier endpoint remains
**999,790 / 999,532 CU under the actual 1,000,000-CU cap** on the two genuine
fixtures, with only 210 CU margin on the larger run.

## First remaining proposition

Identify the pinned research callback's actual pre-q22 visible history and
memo table and prove `FreshFrom` for the reached q22 branch, or compose the
explicit cache-hit loss. Separately bind the actual secure-circle inner
rejection sampler to the ideal OOD subtype before applying the new outer
three-attempt retry law.

After that, universal actual-source joint C1/H1/G affine-image compatibility
including `p0/p2`, the causal posterior simulator, seed/C2/eight-way commitment
composition, retry/publication accounting and coherent pre-beta quotient-pair
extraction remain open. Full privacy and full soundness are not proved.
