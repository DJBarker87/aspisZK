# Deployed native-link disposition audit

**0 RESTORED; 11 still SUSPENDED; 0 native-behaviour FINDING. Target not yet established.** This is a suspended-row handoff, not completed restoration or proof of deployed privacy.

Branch `codex/pv-rdb2-20261028`, base `6273e62061`; exact worktree `/Users/dominic/ZK/.worktrees/pv-rdb2` retained. Dedicated host directory created as requested. No push, merge, crates/programs edit, release ELF rebuild, key creation or key cleanup.

| Row | Disposition | Fresh native validation | Exact remaining obligation |
|---|---|---|---|
| [V229](V229.md) | SUSPENDED B | both original/owned fixed-row tests pass | Layout repeat/alignment and pointer laws; full std association. Project checker recovered/pass. |
| [V230](V230.md) | SUSPENDED B | unit-input masks original/copy match | Layout repeat/alignment and pointer laws; complete structural checker/instantiation binding. |
| [V231](V231.md) | SUSPENDED B | 1,024 full SHA state/buffer/output cases | Deployed pointer/borrow/source-cone laws. Original wrapper checker passes. |
| [V238](V238.md) | SUSPENDED B | 1,024 Ct left/right cases | Deployed pointer/copy/source-cone laws. Original wrapper checker passes. |
| [V239](V239.md) | SUSPENDED B | constant-seven 1,024-cell column at zero point | Layout/pointer laws and complete original/copy structural binding; sample does not cover arbitrary columns. |
| [V240](V240.md) | SUSPENDED B | 768 canonical compressor pairs, lengths0/1/2/16/31/64 | NonNull cast/ref body laws and precise source/call boundary. |
| [V247](V247.md) | SUSPENDED B | 320 sums, 896 pole values, 128 pole errors | NonNull cast/ref body laws and precise source/call boundary. |
| [V256](V256.md) | SUSPENDED B | 4,402 gamma original/copy pairs | NonNull cast/ref/mut laws, mutable restoration and precise source/call boundary. |
| [V257](V257.md) | SUSPENDED B | 4,402 ordinary original/copy pairs | NonNull cast/ref/mut laws, mutable restoration and precise source/call boundary. |
| [V258](V258.md) | SUSPENDED B | weights constructor/materialize/value/bounds tests | Pointer/std body laws and allocation/source/instantiation association. |
| [V259](V259.md) | SUSPENDED B | same weights constructor/materialize tests | Global allocator/Box intrinsic/pointer laws and resource-family association. |

Per-row JSON retains each exact changed function/source span and every unresolved conservative source association; compressed source-gate files retain actual deployed source items. These conservative envelopes are not dynamic call certificates. Some B entries have identical function bodies but changed enclosing items/impls; no behavioural difference is inferred from that classification. Missing mappings and primitive laws are not silently assumed. The nine original-checker gaps were narrowed for V229 only; the other eight remain unrecovered/rebound at their complete boundary.

All native suites used rustc1.94.1, release opt3, debug assertions/overflow checks off, panic=unwind, and the recorded deployed project/dependency features, including zeroize1.9.0. Each receipt contains every resolved crate feature list, compressed metadata SHA, fixture/source pins and the profile. Source audit matched535 present runtime files,1289 installed deployed snapshot files, and all5673 external Lean objects, including their actual search-path selection. No Kani was run or re-credited; K-1/K-2 quarantines remain. No XR import or model was used.

The new `R1Z.PV_RDB2_Layout.same_result/same_failure` proves a **value-level natural-number** transport: on an already-padded element size, the historical checked `n-1` product plus extension and deployed checked `n` product preserve success/error. It does not prove native Layout guards, padding, pointer provenance, allocator effects, compiler correctness or any suspended row. First attempt41100 failed on zero-product definitional normalization; changed proof41101 passes. Combined focused audit41197 passes with exactly `[propext, Quot.sound]`,0 swaps. Exact targets, revisions, timings, RSS and axioms are in [combined-audit.json](combined-audit.json). No historical callback cone is claimed replayed; the restored-row replay set is empty.

Budget used:3/100 Lean attempts (41100,41101,41197),11/120 native capped scopes (9 fixtures+2 source gates),0/0 Kani. Remaining97 Lean/109 native; no budget-exhaustion or infrastructure-failure claim. The unresolved source proofs are retained obligations, not discharged by stopping at a guard or by using the remaining budget on repeated finite tests.

Before/after endpoint premises: removed0, added0, changed0. Existing Lean/model statements remain unrefuted. Deployed source/executable association, E1/E2, real RunJoin, client proof-account route and L1/L2/L3 remain. T is exactly entropy_law/entropy_kernel/observation. Observer and simulator unchanged.

Next concrete deliverable: a faithful deployed1.94.1 NonNull/copy/borrow law at the actual pointer-model boundary, plus concrete dictionary/call association, then the padded Layout/allocator/Box intrinsic laws for rows that allocate. Only after those and complete project structural binding should an actual row law/installation cone be replayed and restored. Existing passing finite tests should be reused unless their inputs change.
