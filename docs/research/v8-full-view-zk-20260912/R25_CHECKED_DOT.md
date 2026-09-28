# R25: checked-dot boundary and measured reconstruction lowering

2026-09-28. Parent `dbc8d7430936e2c06b4895fd6671cbe2343e2373`.
Isolated branch `research/v8-r25-checked-dot-20260928`.
Unchanged R19 proofs, protocol, sparse G, T163, transcript and wire format.
No auxiliary proof system, deployment, settlement or wallet operation.

## Complete execution results

| Exact candidate | World 0 CU | World 1 CU |
|---|---:|---:|
| Pushed R24 control | 1,690,509 | 1,691,993 |
| R25 checked-dot boundary | 1,672,860 | 1,674,376 |
| Also bounded reconstruction additions | 1,647,658 | 1,649,182 |
| **Also explicit nine-channel reduction (selected)** | **1,637,329** | **1,638,823** |

Selected candidate saves **53,180 / 53,170 CU** against R24, approximately
3.1%. It is approximately 42.9% below the frozen R20 endpoint. Another roughly
39% reduction is still required. **Every actual 1,000,000-CU run still
exhausts. The target is not achieved.**

Each candidate passes both complete honest executions at the diagnostic cap,
all 3,281 host wire controls (3,280 checked rejections), the retained corrupted
final checked rejection at the diagnostic cap, and a stack-safe SBF build.
Heap remains 262,144 bytes and simulated accounts remain unchanged.
An exhausted malformed-proof run at 1M is explicitly a resource failure,
not a validation rejection. The second independent reference verifier is not
being counted as a new saving.

## What changed and what was checked

1. `r25_checked_dot` validates the same length limit and every operand limb,
   then calls the existing guarded schoolbook product. Its running sum uses
   widened canonical addition rather than the general checked field-add path.
   The invariant is local: zero is canonical, the unchanged product reducer
   returns canonical limbs, and one conditional subtraction preserves that
   invariant. No public field API or general fallback is weakened.
2. The R24 reconstruction reduces all nine arbitrary u64 channels before
   combining them. Multipliers 3d, 2f and 3e therefore have bounded canonical
   operands. Replacing these with explicit wrapping additions retains the
   already established nonnegative, below-10P evaluation; it removes checked
   wide multiplication lowering without disabling overflow checks globally.
3. Nine explicit calls to the same reducer replace a nested by-value array
   map. Every source input and reduction is retained in the same order. This
   changes computation organization, not the field operation.

All three stages compare the actual old and new dot adapters on **576 vectors**
of lengths 0 through 4,096, including zero and maximal canonical limbs, plus
**7,272 noncanonical cases** and two length errors. The last two stages also
run **600,192 small-dot comparisons** (200,064 vectors, arities 2/3/4) against
independently reconstructed sums of schoolbook products. Those tests cover
the actual changed reconstruction caller, not a disconnected model.
R24's independent frozen-field reconstruction comparisons remain retained;
they were not rerun without a covered source reason.

## Executed-instruction attribution

Each trace uses the actual clean ELF, verifies byte-identical `.text` against
the unstripped symbol artifact, and reproduces the clean full world-0 CU.

| Candidate | Instructions | `__multi3` entries |
|---|---:|---:|
| Checked dot | 1,566,017 | 501 |
| Bounded reconstruction additions | 1,540,815 | 57 |
| Explicit reduction (selected) | 1,530,486 | 57 |

The first trace exposed 444 wide-helper calls introduced by the earlier
flattened reconstruction. The second removes exactly those 444. Remaining
calls are separately attributed, mostly allocator/length arithmetic; this is
not a claim that all helpers are gone. The last rewrite removes 222 further
calls and 9,328 load/store instructions, net 10,329 fewer instructions.
Some inlined work moves into callers, so a caller's exclusive count rising
does not imply the complete execution regressed.

The selected trace still attributes 342,679 exclusive instructions to 2,269
QM31 multiplication entries, 164,750 to packed beta combination, and 117,405
to the checked dot. These are measured remaining targets, not removable costs
or forecasts. The 1M gap cannot be closed by counting these intervals twice.

## Focused formal result

`tools/R25CanonicalSum.lean` proves `sum_bound` and `canonical_add`: for
natural representatives a,b below P, their sum is below 2^32 and a single
conditional subtraction gives the canonical residue modulo P.

Compiled directly with `lake env lean` in the existing cached Lean 4.31
workspace: **exit 0; wall 0.96s; peak RSS 798,392 KiB; swap 0**. Source revision
is the parent above; exact source SHA and command are in the retained metadata.
`#print axioms`: `sum_bound` uses `propext`, `Quot.sound`; `canonical_add` also
uses `Classical.choice`. No `sorryAx`.
This is an arithmetic leaf, **not Rust/SBF refinement or a privacy theorem**.
R24's generic reconstruction identity and numeric bounds still apply unchanged.

## Reproduction and evidence

The selected NUC workspace is
`/home/dombarker/project-offloads/aspis-r20-reduction-array-20260928-a`.
All **180 source pins** are checked before compilation/execution.
Manifest SHA256:
`1b8e72b8fb815330a2f178c6d9cff98beda1416e2e6aaa878160bb275bb89c15`.
ELF SHA256:
`a7ddcdaf5dfbd42789d7a0f869566ccdd89700a3d782f70f8a2ab93e1e3f37b8`.

Stage in order with `stage_r25_checked_dot.py`,
`stage_r25_reconstruction_width.py`, `stage_r25_reduction_array.py`, starting
from `/home/dombarker/project-offloads/aspis-r20-simple-dot-20260928-c`.
Each accepts `--control` and a fresh `--output`; refuses altered source pins.
Use `run_r23_full.py --stage STAGE --mode host|sbf|svm` sequentially.
The retained directory names `r24-host-a`, `r24-sbf-a`, `r24-svm-a` are runner
conventions, not claims that these were the older sources.

All compilation and arithmetic gates are optimized, locked, offline and reuse
caches. Build-host scopes: builds MemoryHigh=5G, MemoryMax=7G; runtime 2G/3G;
trace analysis 1G/2G; focused Lean 2G/3G; all MemorySwapMax=0, TasksMax=128.
No simultaneous heavy build scopes or cold Lean dependency build were needed.
The Solana development skill's source/stack/runtime gates were applied;
complete execution and malformed-input behavior, not host speed, decided which
candidates were retained.

Compact source deltas, logs, source manifests, trace hashes and receipts are in
`evidence/r25-checked-dot`. Large raw traces/ELFs remain on the NUC; keys are
not included or deleted. `tools/check_r25_evidence.py` checks the retained
hashes and exact gate outcomes without repeating unchanged expensive tests.

## First remaining security proposition, distinct from CU

For each admissible actual pre-challenge source prefix and same-public witness
change, establish a legal C1/H1 correction retaining the channel p0 message
whose induced target lies in the **actual 626-equation G image**, or identify
and bound the source-specific exceptional set. The two retained affine source
fixtures do not prove that universal/adaptive compatibility or posterior
preservation. No new dense schedule/rank search was substituted for this task.

Coherent pre-beta extraction of the original quotient pair, shared-oracle
challenge laws, seed/commitment source correspondence and retry/publication
obligations also remain open. The beta sampler allows zero; no nonzero-beta
premise may be silently introduced. C1's negative regression, fixed-block
hiding, local image calculations and full-transcript privacy remain separate.
**This checkpoint proves no new global privacy or soundness result.**
