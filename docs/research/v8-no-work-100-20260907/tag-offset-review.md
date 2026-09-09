# Fixed tag-offset plans: measured complete-transaction saving

Research continuation of `623a01027e88d3324c8e9e7969b28505a8947fa6`,
2026-09-09. Production, main, proof grammar and transcript are unchanged.

## Outcome

| Complete transaction | Previous maximum observed | New maximum observed |
|---|---:|---:|
| Transfer, current page | 1,102,838 | **1,096,831** |
| Transfer, rollover | 1,115,384 | **1,109,377** |
| Withdrawal, current page | 1,120,525 | **1,114,518** |
| Withdrawal, rollover | 1,133,805 | **1,127,798** |

The rewrite saves **6,007 CU on each of twelve identical maximum-body proofs**.
Worst-observed headroom under the actual 1,200,000-CU TxV1 cap is **72,202 CU**.
Each execution includes Registry/account authentication and atomic Pool
settlement, with the pinned classic SPL Token 3.5 SBF on successful withdrawals.
These are three predetermined proofs per shape, not a universal CU bound.

The 24-case maximum-body matrix, 24-case ordinary-body matrix and two
post-real-verifier Token-CPI-failure rollback controls pass. Tested altered
proof, wrong-release, stale-lane and replay outcomes match the prior build;
protected accounts remain unchanged. The failure controls retain their
deliberate failing Token processor. Unsupported rollover stale/replay scenarios
are not counted. All execution limits are real 1.2M caps without diagnostic
runtime overrides.

The same-pool selected-V7 control is still cheaper by **56,008 /74,976 /78,153
/78,914 CU** for the four rows. Its original release policy is retained;
V8 retains global overflow checks except the individually range-proved kernels.
See [exact results](tag-offset-results.json) for proof and artifact identities.

## What is redundant, and what is proved

The previous shared kernel already avoids rebuilding S. Its remaining D is a
fixed tag-offset dot product. The selected table determines every selector
index and coefficient; reinterpreting that table for every coordinate at
runtime is unnecessary. [generate_tag_offsets.py](experiments/generate_tag_offsets.py)
emits thirty straight-line balanced plans from the frozen literal endpoint list.

All **272 literal terms** are represented. Two have a publicly fixed coefficient
zero, so **270 nonzero terms** are emitted; two coefficient-one multiplies per
limb become direct loads. No selector is dropped because it is zero in an honest
fixture. The output uses **240 balanced additions per limb** and no additional
heap. The largest plan has 53 terms. A named zero-plan theorem handles an empty
plan should the generator encounter one; no giant concrete reduction is used.

| Checked result | Meaning |
|---|---|
| `CopyTagOffsetModel.machine_eq_mod` | The generated wrapping-word tree equals its integer expression modulo 2^64 |
| `eval_bound`, `complete_raw_bound`, `all_intermediates_bounded` | Under canonical limbs and the literal count/offset limits, every intermediate is bounded, with total at most 78,855,599,481,120 |
| `machine_exact` | No wrapping occurs for those inputs: the machine model equals ordinary integer arithmetic |
| `CopyTagOffsetPlans.value0` through `value29` | Every generated tree equals the original literal polynomial for arbitrary input limbs |
| `machine0` through `machine29`, `every_machine_exact` | The complete selected family has the same exact raw D values as the reference |

The generated theorem compares **integers**, not just field residues. Therefore
the previously proved reduced-S rotation and final accumulator interface in
`CopyTagShared` is reusable unchanged. Both canonical field output and its range
remain the same. No nonzero challenge or honest-residual premise is added.

The generator independently compares coefficient vectors and checks the pinned
scatter generator/table. The actual source patch adds an independent u128
reference over `COPY_TAG_TERMS`: **61,440 limb comparisons** across arbitrary,
basis, zero, one and all-maximum canonical inputs. The optimized selected copy
module passes all thirteen tests, including existing literal/host-reference
copy and registry comparisons.

This is a kernel-checked algebraic/integer/word model plus actual Rust
differential testing and full SBF execution. It is **not** an Aeneas translation
or a universal Rust/compiler/verifier equivalence theorem. Parser canonicality,
image gate, shifted rows, query batching, authentication and terminal checks
are not changed. The patch is an isolated overlay in a task-owned NUC source
copy, not an edit to the production crate in the research worktree.

## Evidence, provenance and cost

Focused Lean uses 4.32.0 and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, with checked source/olean provenance
for the existing `CopyTagSplit` dependency. No unchanged proof suite is replayed.

| Target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| CopyTagOffsetModel | 0 | 10.86 | 2,879,569,920 bytes | 0 |
| CopyTagOffsetPlans | 0 | 2.52 | 2,963,980,288 bytes | 0 |
| Optimized actual-source tests, including compile | 0 | 32.69 | 662,324 KiB | 0 |
| Quiet SBF build | 0 | 33.49 | 589,936 KiB | 0 |
| Instrumented SBF build | 0 | 33.38 | 589,748 KiB | 0 |

The retained final axiom audits contain only standard `propext`, `Quot.sound`
and, for the finite selector aggregation, `Classical.choice`; the zero-plan
lemma is axiom-free. No `sorry` or new axiom is retained in claimed results.
Two failed small generated-leaf preflights are archived separately: Fin
coefficient/index syntax left distinct atoms to `ring`, and the first finite
selector syntax had an impossible-branch elaboration problem. The generator
was corrected, including a two-table shallow selector. The emitted Rust was
unchanged throughout. Failed logs are not proof evidence.

NUC builds use High5/Max7 GiB, jobs2; SVM uses High3/Max4 GiB. Every scope uses
`MemorySwapMax=0`. The pinned environment is Rust1.94.1 for host tests,
cargo-build-sbf2.3.0/tools1.54, optimized checked SBF Rust1.89-dev, and
LiteSVM0.16.0/runtime4.2.1. The winning release settings remain opt3/fatLTO/
codegen1/overflow-checks=true, with the previous bounded wrapping kernels.

Quiet selected ELF: **999,264 bytes**, **+30,088 bytes** over shared-tag.
SHA256 `def9b544e9b32ffbe38ebaca919b9b9734650349dd8af8abe1597ff582d4ef45`.
Its direct-r10 audit reports 4,096 bytes at emitted entry/panic labels with
no new frame warning. This is emitted-code evidence, not a full stack proof.
The instrumented ELF is 1,002,576 bytes and also passes that audit. No extra
heap, proof field, nonce, transcript input, round or query is introduced:

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

Patched NUC source SHA256:
`73cc46335e72709042021d5b5e60b14cdea727862715ff75274baa43a87e6477`.
Generated Rust SHA256:
`505cfe02bc5b98b767d51fe0331d043ec8d8ccbda6e373d3d89234f45f3a7ea4`.
Pool, Registry, Token and the transaction driver retain their prior hashes,
recorded in [results](tag-offset-results.json). Only synthetic public execution
logs, not proof/witness binaries or owner secrets, are archived. Prover time,
search time and proving RSS were **not remeasured** for this verifier-only change.

## Fresh profile and the next bounded experiment

A separate instrumented complete withdrawal-rollover run uses the same
maximum-body proof2. Its total is **1,133,218 CU**, including instrumentation;
the quiet same-proof measurement above is **1,127,798 CU**. Profiling intervals
include checkpoint overhead/codegen effects and are not standalone CU forecasts.

| Profile interval | CU |
|---|---:|
| Packed canonical decoding and gamma recombination | 159,347 |
| Internal two-tree authentication | 145,913 |
| Ordinary/image preparation | 65,524 |
| Poseidon terminal | 58,856 |
| Other semantic-terminal arithmetic | 58,679 |
| Copy terminal | 56,292 |
| Grouped terminal weights | 40,845 |
| Final coefficient folds | 39,854 |
| Structured terminal weights | 34,464 |

Retain the fixed-offset kernel: measured savings exceed its code-size cost.
The next candidate is **fixed-width specialisation of the remaining C1 gamma
dot loop**, preserving all canonical decoding and helper products. Inspection
of `query_arithmetic.rs` shows that it still loops over six four-product chunks,
four output limbs and four slots. The gamma powers are already prepared once,
and partial reductions are already installed; neither saving may be counted
again. A candidate must prove the same 26-term dot/reduction result and all
intermediate ranges, then beat this complete build under identical proof hashes.
Reject a larger straight-line kernel if instruction footprint or stack cost
outweighs removed loop/index work. Authentication already shares the two-tree
walk, so another duplicate-walk saving must not be assumed.

This gives a concrete, measured next target. It does not establish that all
optimization opportunities are exhausted. Matched-V7 parity, universal CU
coverage, global recovery, adaptive full-view ZK and resource-bounded FS remain
separate gates. No work factor is credited to security.

## Reproduction

Locally, run `generate_tag_offsets.py --check`, then
`run_tag_offset_lean.sh CopyTagOffsetModel NEW_ABSOLUTE_LOG` and
`run_tag_offset_lean.sh CopyTagOffsetPlans NEW_ABSOLUTE_LOG` only when those
sources/import artifacts need checking. The latter checks the retained model
source/olean hashes. On the pinned NUC copy after the shared-tag overlays:

```sh
bash experiments/run_tag_offset_nuc.sh prepare NEW_PREPARE.log
bash experiments/run_tag_offset_nuc.sh test NEW_TEST.log
bash experiments/run_complete_build_nuc.sh tag-offset NEW_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh tag-offset NEW_DIRECTORY
ASPIS_V8_TAG_OFFSET=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
bash experiments/run_complete_build_nuc.sh tag-offset-profile NEW_PROFILE_BUILD.log
bash experiments/run_tag_offset_profile_nuc.sh NEW_PROFILE_DIRECTORY
```

Here `experiments/` abbreviates this research directory's path. Remove only
`ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary-body matrix. Retain the driver's
1.4M CLI runtime setting with the separately declared actual 1.2M transaction
cap; changing that CLI invokes the old diagnostic override/heap path.
`audit_tag_offsets.py` checks archived results, proof identities and proof/source
logs without replaying unchanged heavy suites.
