# L2 leaf trace work — 2026-10-25

Target: D166 simulatable source traces for the unchanged leaf kernels of D187.
Baseline: 970912bfe7ad33e9b53eb7d65a4c47ae129b3696, branch
codex/cx-l2-leaf-20261025. No adoption or deployed privacy claim.

## Stage 1: source and contract

The observation includes branch outcomes (including short-circuit comparisons),
array addresses, loop visits, allocation requests, variable-latency arithmetic
calls, and collection operations. Allocation failures, allocator internals,
stdlib sort/Vec cost, hashing, process/TLS initial state and panic behavior need
explicit semantics; deterministic Rust output is not a proof of their costs.

| Kernel | Source inputs controlling local trace | Additional obligations |
|---|---|---|
| SeedExpander / Profile21 m31 | public domain, seed, current counter/block/word, candidate words; cap 16 | hash-source relation, refill/cursor across four limbs and failures |
| two-seed nonzero | public nonce, ordered 64-byte OS draws/statuses; cap 16 | byte comparison cost, short-circuit second seed, failed draws |
| division / gamma / circle | raw 32-byte FS answer, public circle row | quotient operands, gamma carry, inverse/subfield tests and fallback |
| sparse_eq_weights | full ten-coordinate point, including previous challenges and public assignment bits | equality internals; arithmetic kernel trace |
| QueryScan | raw FS block pairs, accepted prefix, draw counter | duplicate search position, extra block boundary and exhaustion |
| multiproof | arity, ordered query indices; node payload excluded from control | well-formedness, node_count, sibling sharing, sort/dedup cost, Vec growth |
| P_R1 | complete R1PublicChallenges, build profile, transport/TLS initial state | actual emit/convert/check arithmetic trace, pivots, early exits, std costs |

These are source dependency classifications, not seven formal refinements.
No direct witness read was identified inside these leaf bodies. Their call
arguments and whether/when they are called can still depend on the witness.
In particular challenge dependence is not the same as independence from the
witness, and private-coin marginal independence is not joint privacy.

## Coupling boundary

`R1Z.ProverCommitQuotientCoupling.completed_view` and `middle_completion`
preserve `view`/`retryTest` after tape completion. Their conclusions do not
retain raw sampler words or a source-cost trace. `meanM_Q` proves the completed
middle tape law, not equality of the real source trace paired with that tape.
`R1Z.SideChannelL1JointCoupling` explicitly leaves concrete joint agreement
open. `SideChannelEntropy.count_history_preserved` preserves draw counts,
not short-circuit byte positions under arbitrary successful-seed permutations.
Thus none can be used as an unconditional joint-input coupling for this task.
No freshness, independence or cost premise is silently added.

## Build availability

The documented launcher path without `/tools/` is absent. The existing
`/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh`
accepts only J5000–9999 (literal shell case), whereas this task owns J11400–11599.
No launcher was changed or copied. Lead was asked for a configured launcher.
A local `lake env lean --version` in AspisFormal started a cold mathlib clone;
it was immediately interrupted before any build. Focused Init-only modules can
use the installed 4.32 toolchain from the worktree root without that package.
