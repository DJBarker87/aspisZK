# R54: bounded wrapper laws and exact-field circle policy

Base: `eaa0435c1e71b9605af40daf7b07cefd3bcb5e92` (pushed R53).
Branch: `research/v8-r54-sampler-wrappers-20260929`.

## Exact result

35 new Lean theorems compile with 35 axioms audits, using standard Lean axioms
only. Source-shaped cap-three nonzero, OOD and secure-circle wrappers now
have exact causal-program/deterministic-run correspondence and R52's
memoized-oracle law. Rejections retain the advanced state and full hash trace;
inner exhaustion stops immediately. The nonzero wrapper shares its source
error for both exhaustion paths, whereas OOD and circle retain distinct
inner and outer error variants. No zero fallback or resampling of used masks
is introduced.

The actual unchanged Rust nonzero/OOD APIs match 358 Lean-exported fixtures
byte-for-byte: 2,684 hash calls, eight cache hits, all returned values/errors
and all final states. This is finite differential evidence, not universal
Rust extraction or an independent-uniform source challenge theorem.

## Compiled boundary

| Leaf | New theorems | Result |
|---|---:|---|
| BoundedSamplerWrapper | 7 | Exact bounded execution, complete trace, immediate error/success, canonical successful input |
| SamplerWrapperPolicies | 8 | Literal nonzero/OOD policies, cap three, exact program laws and accepted-word invariants |
| SamplerFieldDecode | 7 | Canonical words into exact QM31; zero and CM31 tests agree with the decoded field |
| SamplerCirclePolicy | 13 | Ordered singular/subfield rejection, rational map, denominator, inverse, injectivity, OOD and bounded program law |

WrapperReplay is a fifth compiled executable leaf, not an extra theorem.
The final reused cache has 286 successful objects, including two missing
unchanged predecessor leaves (CircleChord and ExactTowerChord). New-leaf
compile time totals 9.45 seconds, peak RSS 3,307,660 KiB, zero swaps.
Every exact target, command, source hash, exit, timing and axioms audit is
retained under `evidence/r54-sampler-wrappers`.

The circle algebra uses the previously proved exact deployed tower, not a
new field or hiding assumption. The roots of `1+t²=0` are `±i` in CM31, so
an accepted outside-CM31 parameter has a nonzero denominator. The source's
singularity-first error order remains explicit. Its map is
`((1-t²)/(1+t²), 2t/(1+t²))`, lies on the circle, recovers `t` as `y/(1+x)`,
is injective on finite parameters, and cannot have both coordinates in CM31
when `t` is outside CM31. These are algebraic statements; the Rust `try_inv`
implementation has not been universally refined by this milestone.

## New actual-source execution

For each of the nonzero and OOD wrappers:

- 48 successful schedules spanning all three acceptance attempts and varying
  per-limb rejection counts.
- 96 inner failures spanning all three outer positions, all four failed-limb
  positions and eight preceding rejection patterns.
- 32 outer-exhaustion schedules.
- Three frozen-state controls: success, repeated outer rejection and inner
  exhaustion.

Total: 179 cases per API, 358 overall. This is not exhaustive over all raw
words or all rejection schedules. The executable Lean oracle programs and
actual Rust compare every input/output byte of the script, not only digests.
No new circle-output Rust comparison is claimed. The model's mathematical
circle inversion is noncomputable and intentionally not disguised as a
word-level execution test.

Fixture export: 1.68 seconds, 3,241,292 KiB peak RSS, zero swaps.
Optimized Rust compilation: 19.01 seconds, 518,472 KiB peak RSS, zero swaps.
Source replay: 0.00 seconds at the timer's displayed resolution, 2,112 KiB
peak RSS, zero swaps. Cargo used release/offline/locked mode, two jobs and
retained overflow checks. Source pins preserve the 197-file control apart
from the test-only Cargo entry and add just the new replay source.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r54_evidence.py
```

## First remaining proposition

Prove universal correspondence between the actual Rust sampler/field
execution and these exact byte/field programs, beyond finite replay. In
particular, circle `square`/`try_inv`/multiplication must implement the
mathematical guarded map on canonical inputs. Then compose those programs
with the complete actual prover/observer chronology, including prequeries,
first reads, shared seed/commitment operations, retries and publication.

The exact memoized model law does not say the emitted challenges are
independent uniform variables conditional on later roots or acceptance.
R50's degree-819 fixed-root polynomial therefore still has no justified
numerical source failure bound. Joint coverage, the remaining semantic
cuts, simulator construction, commitment/seed hops and pre-beta extraction
soundness remain separate obligations; none is waived here.

No production verifier, protocol, negative regression or wallet changed.
No deployment/merge or SBF rerun. Selected R27 CU remains
1,620,236 / 1,621,719, with both actual 1M-cap runs exhausted.
Full privacy and supported-budget completion are still open.
