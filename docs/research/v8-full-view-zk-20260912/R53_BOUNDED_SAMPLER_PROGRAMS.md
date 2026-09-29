# R53: bounded sampler programs and actual-source trace replay

Base: `a26a468746e9551769ce1d17104050e1fc1bf1fc` (R52).
Branch: `research/v8-r53-bounded-sampler-programs-20260929`.

## Result

37 new Lean theorems compile, with 37 axioms audits using only standard Lean
axioms (or no axioms). The two bounded core samplers are now causal oracle
programs, preserving all hash calls, cache-hit behavior, outcomes and final
states. Their complete-oracle execution equals R52's first-read-only
memoized interpreter. This is an exact model theorem, not an independent
uniform-challenge assertion after conditioning on later transcript data.

The executable Lean programs generated 4,753 fixtures. The unchanged actual
Rust transcript implementation matched their returned results/errors, final
32-byte states, and every hash input and output byte: 26,472 hash calls,
including 20 cache hits. These finite differential tests do not constitute
universal Rust extraction or a source privacy theorem.

## What compiled and was proved

| Leaf | Theorems | Boundary |
|---|---:|---|
| SamplerWords | 7 | Little-endian words, masks, lengths and range bounds |
| QM31SamplerProgram | 6 | Shared block cursor, per-limb rejection cap, exact program/run trace |
| Q22WordScan | 7 | Duplicate filtering, progress, 22-query/64-draw bounds, detection timing |
| Q22SamplerProgram | 5 | Exact program/run trace and unfuelled operational relation |
| QM31SamplerInvariants | 3 | Successful output has exactly four canonical limbs |
| SamplerOracleLaws | 3 | Exact memoized-oracle laws for both core samplers |
| Q22SamplerInvariants | 6 | Distinct bounded successful queries; exact failure-count range |

SamplerReplay is an eighth compiled executable leaf, not an additional
theorem. New-leaf compile time totals 12.10 seconds; peak successful RSS
3,282,552 KiB; zero swaps. The final reused cache has 279 successful objects.
Exact per-target commands, source hashes, statuses, timings and axioms output
are retained under `evidence/r53-bounded-sampler-programs`.

QM31 starts with a mandatory squeeze, permits eight attempts per limb,
shares the word cursor across the four limbs, refills only when needed and
discards unused words on return. Failure retains the advanced state. Q22
models the selected source call `(count=22, bound=2^18, max_draws=64)`;
the general API's invalid-argument branches are not claimed here. Its
source-shaped operational relation has no artificial fuel outcome: eight
blocks suffice by the scan-progress invariant. Completion on the last word
of a block can require an additional detection block, exactly as in Rust.

## Executed source checks

- 4,096 successful field rejection-count patterns (8^4), with representative
  canonical words/high bits, not exhaustive enumeration of raw u32 values.
- 585 field failure schedules across the four limb positions.
- All 43 possible q22 first-completion positions from 22 through 64.
- 21 q22 failure distinct-count cases.
- Four frozen-state/cache cases and four consecutive-two-field-call cases,
  retaining the unused-block-suffix discard rule.

Totals: 4,684 field cases, 65 query cases and four consecutive-call cases.
The oracle is a deterministic memoized script, not a claimed SHA distribution.
Lean export: 3.84 seconds, 3,236,596 KiB peak RSS, zero swaps.
Optimized Rust compilation: 18.62 seconds, 518,460 KiB peak RSS, zero swaps.
Actual-source replay: 0.03 seconds, 1,936 KiB peak RSS, zero swaps.

The fixture's uncompressed SHA-256 is
`0c54f42689e50f9f3e91a7625db463009a493b458beccc74ece18f3477abbdbd`.
The source manifest preserves all 197 parent pins except the test-only Cargo
entry, adds the replay target, and leaves transcript/verifier source unchanged.

Check the retained evidence without rebuilding:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r53_evidence.py
```

## First remaining source-specific proposition

Establish universal correspondence between the actual Rust bounded sampler
semantics and these oracle programs, beyond the finite trace replay. The
nonzero, OOD and secure-circle bounded wrappers must also be compiled with
their exact rejection predicates, failure variants and state chronology.
Then compose the complete prover/observer experiment, including prior oracle
queries, retries, first hits and publication selection. A known-state caller
can deliberately prequery the next address; no unconditional freshness or
rare-collision premise is introduced here.

R50's fixed-root polynomial is still not a numerical source probability bound.
Joint H1/G coverage, all semantic cuts, simulation/commitment/seed hops,
pre-beta extraction soundness and optimized Rust refinement remain separate
obligations. No used masks were resampled; no negative regression was removed.

No verifier or protocol change, new SBF run, wallet operation or deployment.
Selected R27 CU remains 1,620,236 / 1,621,719; both actual 1M-cap runs exhaust.
Full privacy and the supported-budget goal are not complete.
