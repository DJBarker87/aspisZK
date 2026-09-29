# R77: complete QM31 challenge value/state bridge

Base revision: `8b8a8e43a498cbf294e9e4f132a9dc5a22ede2fc` (R76).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact proved boundary

The actual generated `Transcript.challenge_qm31`, under the explicitly
constructed total deterministic hashv adapter for arbitrary `H`, returns
exactly the encoded value/error and transcript state of the retained
`QM31SamplerProgram.challengeRun`. The theorem covers the initial squeeze,
shared block/cursor across limbs, each limb's eight-attempt rejection limit,
early exhaustion, mutable write-back and final QM31 reconstruction.

`SamplerWriteback.bounded_matches` proves the mutable-loop result against the
model's accepted list for every remaining iterator length. Successful writes
are represented in the same deferred order as the source closures; a separate
four-slot lemma reduces them to the expected four encoded values. On error,
the internal partial array is existential, but the externally returned error
and advanced state are exact. No premise about that unobserved array is used
to infer the returned value or state.

`SamplerChallengeBridge.challenge_exact` composes that result with R73's
squeeze bridge and R75's actual entry theorem. The model's proved length-four
invariant rules out malformed success lists. Corollaries establish exact
exhaustion, exact success, and canonicality of all four components of every
successful source result.

## Important scope distinction

This is the complete **QM31 challenge value/state** correspondence under the
explicit adapter. It is not yet a complete observed hash-query-history
correspondence, concrete SHA backend/ideality theorem, or the full circle
sampler theorem. Equality for the returned-value projection must not be used
as if it proved the model's trace projection. The existing circle proof also
uses a different extracted namespace and requires explicit transport before
composition with this sampler.

No fresh independent answer assumption, hiding assumption, new axiom or
admitted proof was introduced. Full privacy and soundness remain open.

## Compilation and evidence

Two Lean leaves compile, with **eight theorem audits**. Two use only standard
Lean axioms; six also retain the inherited opaque `core.fmt.Formatter : Type`
through source `unwrap`. The audit remains **PASS_SCOPED**, with that dependency
explicit rather than silently treating it as a standard-axioms-only result.

Lean `leanprover/lean4:v4.32.0`, pinned cached NUC workspace, `-j1 -M4500`.
Actual cgroup: High 5 GiB, Max 7 GiB, SwapMax 0, TasksMax 128. The single final
two-leaf replay reused 330 targets and verified 307 dependency pins.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/SamplerWriteback` | 0 | 2.04 | 3,706,784 | 0 |
| `AspisV8R19/SamplerChallengeBridge` | 0 | 1.99 | 3,707,636 | 0 |

The 34-artifact manifest records exact source hashes, base revision, commands,
axioms, dependencies, resource settings and failed focused attempts. Those
attempts exposed an encoded-cursor normalization mismatch, record-literal
layout, and a zero-cursor representation mismatch. The fixes are explicit;
there was no higher-cap retry or dependency rebuild. Final logs contain no
`sorryAx`.

## First remaining proposition

Establish source sampler observer/hash-query trace correspondence, separately
from the returned value/state theorem, and transport the existing circle-map
proof into the actual R72 sampler namespace. Then compose the full circle
sampler, including its three-attempt outer retry loop and errors.

Beyond this sampler boundary, shared-oracle/seed/C2 justification, complete
joint-view simulation, failure/retry/publication loss accounting and coherent
pre-beta quotient-pair extraction remain open. The C1 negative regression and
local masking results retain their separate meanings.

No runtime/protocol change, new CU measurement, deployment or wallet operation.
Retained complete CU: **1,495,663 / 1,497,050**, both actual 1M-cap runs exhaust.
