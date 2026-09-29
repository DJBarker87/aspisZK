# R78: actual circle-sampler value/error/state bridge

Base revision: `1eff875d763b8d7b591d12f9e5b5138de4fed250` (R77).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact proved boundary

`SamplerCircleBridge.source_exact` proves that the actual extracted
`Transcript.challenge_secure_circle_point`, under R73's explicit total
deterministic hashv adapter for arbitrary `H`, returns exactly the encoded
value/error and updated state of the retained bounded-wrapper algorithm.
The wrapper uses the existing `SamplerCirclePolicy.accept`, with the actual
source error constructors, and the source's three-attempt limit. No model
error is silently collapsed: inner challenge exhaustion and outer parameter
exhaustion stay distinct.

The generic `bounded_exact` theorem holds for every outer retry count and
every state. It composes R77's complete QM31 sampler with the actual R72
circle arithmetic. Each candidate has the proved canonical limb bounds;
the circle computation preserves singular-before-subfield rejection order.
Rejected circle candidates retain the advanced transcript state; inner
exhaustion stops immediately. Neither successful draws nor independent hash
answers are premises.

The successful-result corollary proves both source point coordinates are
canonical, their decoded squares sum to one, and the two coordinates are not
both in CM31. Under the explicit total adapter, no Aeneas backend failure is
returned. That last statement does not assert that an arbitrary failing hash
backend cannot fail: totality follows from the adapter's definition.

## Reuse rather than another arithmetic proof

The attempted direct import of the R69 and R72 extractions failed because
Aeneas's discriminant attribute generates the same global instance name,
`instDiscriminantCirclePointErrorIsize`, for their two circle-error types.
This is an import collision, not a failed field identity. The original
extractions, runtime and predecessor proofs were not edited.

`generate_r78_closure.py` instead reuses six pinned R70/R71 proof scripts in
the actual R72 namespace. The transformation is checked exactly: identifier
renaming plus deletion of the unavailable diagnostic `circle_probe`
corollary and its audit. No substantive premise or proof is weakened.
The original hashes are independently frozen in `check_r78_evidence.py`.

The six reused leaves contribute 72 theorem audits. The new composition leaf
contributes five. This is reuse and composition, not 77 newly designed
mathematical results.

## Compilation and evidence

All seven leaves compile on Lean `leanprover/lean4:v4.32.0`, with
`lake env lean -j1 -M4500`. The actual enforced cgroup has MemoryHigh 5 GiB,
MemoryMax 7 GiB, MemorySwapMax 0 and TasksMax 128. Focused predecessors passed
before the one final seven-target replay, which reused 332 compiled targets.
All 344 transitive local/runtime dependency pins were checked on the NUC;
the local audit also checks source hashes and retained runtime pins.

All target names below have prefix `AspisV8R19/`.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `SamplerClosureExplicitWord` | 0 | 1.96 | 3,708,856 | 0 |
| `SamplerClosureProductExecution` | 0 | 4.18 | 3,745,420 | 0 |
| `SamplerClosureProductCorrectness` | 0 | 2.34 | 3,718,180 | 0 |
| `SamplerClosureCircleScalarTransport` | 0 | 1.90 | 3,710,352 | 0 |
| `SamplerClosureCircleFieldExecution` | 0 | 2.43 | 3,721,352 | 0 |
| `SamplerClosureCircleSourceExecution` | 0 | 2.32 | 3,716,212 | 0 |
| `SamplerCircleBridge` | 0 | 2.23 | 3,720,980 | 0 |

The axioms audit has 77 entries: 73 use only standard Lean axioms; four in
the new bridge also retain the previously documented opaque
`core.fmt.Formatter : Type` from the generated sampler's safe unwrap path.
No new axiom, `sorry`, admitted proof or increased resource cap is used.
Final logs contain no warnings, errors or `sorryAx`. The result remains
**PASS_SCOPED**, not a standard-axioms-only claim for the complete sampler.

The 48-artifact evidence manifest retains the failed import experiment and
the first composition attempt. The latter failed only in projecting a
simplified result-pair equality in the success corollary; the exact bounded
and entry equalities already compiled. The corrected projection passed the
focused compile and final replay. Failed logs are diagnostic evidence, not
accepted proof artifacts.

## First remaining proposition

Prove the actual sampler's **observed hash-query history** corresponds to
the retained oracle program, including initial squeezes, block rollover,
per-limb rejection, inner exhaustion, circle rejection and outer exhaustion.
The new theorem uses only the model's returned-value/state projection. Pure
function equality cannot exclude extra or reordered oracle calls and must
not be presented as a trace theorem.

The retained R53 finite Rust observer replay is useful diagnostic evidence,
but is not a universal source-observer theorem. The next source refinement
must supply that missing observation semantics, then instantiate the
retained coherent memoized-oracle laws. No independence, concrete SHA
ideality or hiding premise is silently added here.

Full shared-oracle/seed/C2 justification, complete joint-view simulation,
failure/retry/publication loss accounting and coherent pre-beta quotient-pair
extraction remain open. The C1 negative regression and local masking results
retain their separate meanings. This bridge does not establish global
privacy or full soundness.

No runtime/protocol change, SBF rerun, deployment or wallet operation.
Retained complete CU: **1,495,663 / 1,497,050**; both actual 1M-cap runs exhaust.
