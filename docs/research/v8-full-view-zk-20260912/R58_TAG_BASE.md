# R58: paired Copy tag-base factoring

Base: `e6e2015650ba4104da3797e4c375591ba29e92c0` (pushed R57).
Branch: `research/v8-r58-tag-base-20260929`.
Unchanged repaired protocol, proof bytes, transcript, sparse G and T163.

## Complete execution result

| Primary verifier | World 0 CU | World 1 CU |
|---|---:|---:|
| R57 control | 1,554,448 | 1,555,925 |
| R58 paired tag factoring | **1,540,502** | **1,541,957** |
| Saving | 13,946 | 13,968 |

Select R58. Both distinct genuine proofs accept under the diagnostic cap;
both corrupted combined finals give checked Custom(6) errors. At the actual
1M cap, honest and corrupt cases exhaust. Resource exhaustion is not counted
as rejection. Same driver, 256 KiB heap, proof hashes and unchanged accounts.
The slower fixture is still **541,957 CU above the target**. These results
do not establish a universal resource bound.

## Exact paired source change

The 136 literal link tags equal `B+i`, with `B=1,124,073,472`, `0≤i≤135`.
Static assertions check every link and every generated tag term. The selected
tensor/tag profile now computes tag-coordinate sums using only `i`, and adds
`B` to the base-field limb of every tuple pattern before finishing. Both sides
of this change are required:

`s * ((B+i)+pattern) = s * (i+(pattern+B))`.

No tag, pattern or constraint is removed from the Copy polynomial. Actual
registry rows, slots, append-level/variant selection, multiplicities, low
selectors, four value/weight outputs and final residual stay intact. Other
profiles retain the old tag implementation. The final pattern shift needs a
14-QM31 stack copy; the SBF stack gate passes. No new heap allocation.

Small offsets allow each tag-coordinate limb to accumulate all products into
one u64, with one final canonical reduction. Even raw u32 limbs satisfy
`272*(2^32-1)*135 < 2^48 < 2^64`; every prefix also fits. Explicit wrapping
additions therefore cannot wrap. The existing final reducers remain unchanged.
Field-equivalence tests use canonical inputs, as provided by actual selectors.

The host references are frozen old tag and finish bodies, not aliases for the
changed implementation. The retained R57 full-lane reference calls that frozen
finish, preventing both sides of the comparison from silently changing.
All source edits are in reproducibly staged research copies, not production
repository protocol paths.

## Executed checks and formal boundary

The optimized actual-source host checks pass:

- 9,600 tag-coordinate comparisons, including all 64 high-coordinate positions
  in each of four field limbs, zero/maximal canonical limbs and random arrays;
- 640 complete finishing comparisons with arbitrary tuple patterns, high/low
  selectors and both variants; 2,978 cases detect the omitted-base negative;
- retained 544 source terms, 70,720 dynamic weight checks and 512 scratch/full
  Copy-lane comparisons against the original tag and finish;
- 3,281 wire controls, including 3,280 checked malformed-input rejections;
- both honest host proofs, SBF stack gate and complete SVM runs above.

`AspisV8R19/TagBase.lean` proves eight generic leaves: endpoint and list-sum
shift identities, natural tag subtraction, product and list-sum bounds,
accumulator and every-prefix u64 safety, and delayed canonical reduction.
Focused `lake env lean` compile: **exit 0, 1.44 s, peak RSS 3,260,416 KiB,
zero swaps**, Lean 4.32.0. Eight axioms audits use only `propext`,
`Classical.choice`, `Quot.sound`. The cache contains 290 successful
source-pinned targets; unchanged targets were reused, not recompiled.

These leaves prove the arithmetic identities and bounds. They do not prove
universal Rust/registry/compiler refinement or full privacy/soundness.

## Trace attribution and source lock

The complete world-0 trace reproduces **1,540,502 CU** with byte-identical
deployed/unstripped `.text`, executing 1,435,439 instructions. Only these
exclusive function totals change:

| Change | Instruction saving |
|---|---:|
| Old tag-dot body becomes a thin wrapper | 26,719 |
| New whole-coordinate delta sum | −12,588 |
| Pattern-shift/caller overhead | −185 |
| Net | **13,946** |

All other exclusive function totals are unchanged. The old tag-dot total was
26,779 instructions; its wrapper retains 60. No saving is credited twice.

Final stage: `/home/dombarker/project-offloads/aspis-r20-r58-tag-base-20260929-b`.
195-pin manifest: `e24eedc1c69eb9d251a13df9d2d48339a5bacb32ece9ddf6ba0fdbbf2fcc02f2`.
ELF: `6598d002ce8fb7b990b349ee6fbd34274ba1fe46b034592fba6bdac7b33db2ce`.

The first stage passed selected-profile host checks but failed the build's
no-feature host basis-export preflight: the new host reference helpers lacked
the selected-profile feature gate. No SBF artifact was produced from that
stage. Their cfg gates were corrected, a fresh stage was made, and all affected
host/build gates were rerun successfully. The failure log and original stage
manifest remain in evidence; no pin or check was waived.

## Reproduction and resources

Use `stage_r58_tag.py --control R57_STAGE --output FRESH_STAGE`, followed by
`run_r58_full.py --stage FRESH_STAGE --mode host`, `sbf`, `svm`. Capture the
exact unstripped artifact immediately after build before another build uses
the cache. Retained full-trace tools check `.text` equality and clean CU.

NUC systemd scopes: Rust MemoryHigh/Max 5G/7G, Lean 3G/5G, SVM/trace/analysis
2G/3G, staging/collection 1G/2G; MemorySwapMax=0, TasksMax=128. Maximum
overlapping reservation 12 GiB. Release/offline/locked Cargo, two jobs, cached
dependencies, overflow checks enabled. Compilation was the costly phase;
there was no debug arithmetic gate, dense elimination or package-wide replay.
The Solana development skill's source/rejection, stack and complete-execution
checks determined selection. No merge, deployment, transaction submission,
wallet operation, key cleanup or unrelated changes.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r58_evidence.py
```

The checker reconstructs the exact Copy module delta from the pinned parent,
checks all old source pins except the intended Copy/Cargo changes, verifies
the independent references, logs, Lean axioms and unchanged-proof execution,
and verifies the trace delta. Raw registers, binaries and retained build keys
remain on the NUC, outside compact committed evidence.

## First remaining obligations

CU: roughly 542k remains. The current trace still attributes 310,483 exclusive
instructions to general QM31 multiplication, 111,229 to checked dots and
37,272 to prepared multiplication. These are executed instruction counts,
not independent removable CU intervals. Next inspect actual call sites and
operand reuse before selecting another arithmetic candidate; do not repeat
previously rejected backend/inline experiments without a new source reason.
Native semantic and ordinary work remain targets; no promised under-1M result.

Privacy: universal sampler/field source correspondence, including guarded
circle inversion, remains the first source-specific obligation. Complete
prover/observer chronology, joint posterior coverage, all semantic cuts,
shared-oracle/seed/commitment hops, retries/publication and justified loss
bounds remain open. Coherent pre-beta extraction is a separate soundness
obligation. No negative regression was removed, new hiding assumption added,
or full privacy/soundness claim made.
