# R57: source-derived Copy selector gather

Base: `80aa7d98ebbc708ef54b947bb1810b913ddd21ec` (pushed R56).
Branch: `research/v8-r57-selector-gather-20260929`.
Protocol, sparse G, T163, transcript, proof bytes and validation checks unchanged.

## Complete execution result

| Primary verifier | World 0 CU | World 1 CU |
|---|---:|---:|
| R56 control | 1,586,096 | 1,587,563 |
| R57 selector gather | **1,554,448** | **1,555,925** |
| Saving | 31,648 | 31,638 |

Select R57. Both distinct unchanged genuine proofs accept under the diagnostic
cap; corrupted combined finals return checked Custom(6) errors. Both honest
and corrupted fixtures exhaust at the actual 1M cap. No resource failure is
counted as checked rejection. Same driver, 256 KiB heap and unchanged accounts.
The slower fixture remains **555,925 CU over the target**.

## Actual source rewrite

The selected Copy lane used 272 endpoint calls to scatter high selectors into
30 weight slots and 43 pattern slots. Tag coordinates are already computed by
the separate retained tag-dot path. A const builder now derives the ordered
fibres of those 73 slots from the exact same 136-link endpoint registry:
272 weighted terms and 272 unweighted pattern terms.

The new gather evaluates those fibres directly. Each slot accumulates four
u64 limb sums and reduces once at its end. At most 272 u32 terms give a sum
below 2^41, so the explicit wrapping additions cannot wrap. This bound does
not require input canonicality; equivalence to repeated field addition does
use the existing canonical field invariant of actual selectors.

The producer/consumer side, slot, pattern, row, weight kind and append level
remain source-derived. Variant switches and both append-bit choices are kept.
The four final value/weight vectors, tag-dot calculation, pattern calculation,
active selector and final Copy residual are unchanged. Scratch remains the
same 103-QM31 vector; no new runtime allocation or large stack array is added.
The original endpoint implementation and full evaluator remain host references.
Only the selected tensor/tag profile uses the gather; other profiles retain
the original loop. No repository production path was edited.

## Source checks and compiled proof boundary

The focused optimized Rust gate checks:

- all **544 ordered terms** against a separate traversal of the literal
  registry, retaining multiplicities and exact slot boundaries;
- **70,720 weight checks**: both variants, zero/all-one append indices and
  every one-hot/complemented bit position across the full u64 append word;
- **512 scratch and full-lane comparisons** with the original actual source,
  using arbitrary canonical high/low arrays, all 64 high-coordinate basis
  positions, zero/maximal high limbs and both variants;
- both unchanged honest host proofs and all **3,281 wire controls**, including
  3,280 checked rejections;
- SBF stack gate and the complete SVM runs above.

The generic `AspisV8R19/SelectorGather.lean` leaf proves six statements:
canonical sum equals one reduction of the integer sum; permutation preserves
that result; raw-word sum and accumulator bounds; every prefix fits in u64;
and boolean selection equals multiplication by its binary weight.

Focused compile: **exit 0, wall 1.56 s, peak RSS 3,228,812 KiB, zero swaps**.
Six `#print axioms` audits use only `propext`, `Classical.choice`, `Quot.sound`.
Lean 4.32.0 cached workspace, 289 successful source-pinned objects. No full
package replay, large reduction or new axiom. These leaves plus source tests
are not universal Rust/registry/compiler extraction or a privacy theorem.

## Complete traced attribution

The new world-0 trace reproduces clean **1,554,448 CU**, with byte-identical
deployed/unstripped `.text`. It executes 1,449,385 instructions, down 31,648.
After removing Rust hash suffixes, the only exclusive function changes are:

| Function change | Instruction saving |
|---|---:|
| Remove 272 endpoint-scatter calls | 42,549 |
| Remove their binary-selection calls | 2,322 |
| Smaller evaluator caller | 4,387 |
| New gather | −17,610 |
| Net | **31,648** |

All other exclusive function totals are unchanged. This accounts for the full
measured world-0 saving; it is not a universal or worst-case resource theorem.

Stage: `/home/dombarker/project-offloads/aspis-r20-r57-selector-gather-20260929-b`.
Manifest: `2653b3555389aee79eb4866ed94d74131247eb574dd972b07f166c558c491435`.
ELF: `479a387b7cd701cf099fa72b1ac0e13191adadf1ab2c6f85e5e2f530c92bb30b`.

## Pins, resources and reproduction

The initial stage stopped at the exact pin-count preflight before compilation:
the Copy module was not in the older arithmetic-specific manifest, so adding
it increased the count beyond the estimate. No pin was waived. The final
stager explicitly checks the original Copy module and generated registry
hashes, preserves an original source copy, and pins the registry as well as
all new sources. Final count: **193**, retaining all 188 R56 pins except the
expected host Cargo test entry change. The initial 191-pin manifest is retained
as preflight evidence, not accepted compiled evidence.

Use `stage_r57_selector.py --control R56_STAGE --output FRESH_STAGE`, then
`run_r57_full.py --stage FRESH_STAGE --mode host`, `sbf`, `svm` in order, inside
resource-bounded Linux scopes. Final build used release/offline/locked Cargo,
two jobs, cached dependencies and overflow checks enabled. Compilation was
the expensive phase; no debug arithmetic or dense elimination was used.

NUC scopes: Rust 5G/7G high/max; Lean 3G/5G; runtime/trace 2G/3G; staging,
collection and analysis 1G/2G; MemorySwapMax=0, TasksMax=128. Maximum overlapping
reservation 12 GiB. The Solana development skill's source, stack and complete
runtime gates determined selection. No deployment, merge, wallet operation,
key cleanup or unrelated work. Raw trace registers/binaries/build keys stay
on the NUC, outside compact committed evidence.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r57_evidence.py
```

## First remaining boundary

CU: the tag-dot path still spends 26,779 exclusive instructions. Its source
tags share a fixed base plus small offsets. Check whether moving that common
base into the tuple patterns allows bounded whole-coordinate tag sums, while
preserving the complete Copy polynomial. This is an unexecuted next candidate,
not a claimed saving. Remaining native semantic/ordinary work is still needed
to close the 555,925-CU gap.

Privacy: universal sampler/field source correspondence, including guarded
circle inversion, remains open. Complete prover/observer chronology, joint
coverage/posteriors, all cuts, seed/commitment hops, shared-oracle joint laws,
retries/publication and justified loss bounds are not complete. Coherent
pre-beta extraction remains a separate soundness task. No negative regression
was removed, no hiding assumption added, and no full privacy/soundness claim.
