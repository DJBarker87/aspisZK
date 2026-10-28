# PV_RDCD final deployed-source disposition

**8 RESTORED at stated source/Result boundaries; 9 SUSPENDED. Privacy target not established.**

Branch `codex/pv-rdcd-20261028`; exact assigned worktree retained. Candidate base `6273e62061`; D393 resume base `af8459b3e3`. [Full commit log](COMMITS.txt), [resume log](RESUME-COMMITS.txt), [machine-readable audit](AUDIT.json).

No crates/programs changes, pushes, release-pin changes, new trust fields, observer/simulator weakening or key operations. Extraction used the unchanged pinned nightly 1.98 tools with deployed features, dependencies and release settings under ruling (x′); source bodies were compared to 1.94.1, with separate deployed-body laws where needed. Native Rust validation used release 1.94.1. No Kani result was run or re-credited.

| Row | Final status | Evidence / exact blocker |
|---|---|---|
| [V169](rows/V169.md) | RESTORED / B | Concrete Vec/array Default, take/replace, RawVec metadata/frame laws; original extraction and reference transport. |
| [V197](rows/V197.md) | SUSPENDED / D | Pinned Aeneas rejects escaping reference output without loan validation; Range/TryInto/endian cone remains open. |
| [V201](rows/V201.md) | SUSPENDED / D | Original encoder checker passes; 145 concrete ChunksExact/Zip/array-iterator/index records remain unresolved. |
| [V212](rows/V212.md) | RESTORED / B | Exact original adapter and fresh extraction;1.94.1 Option/wrapping/cast/shift laws; complete importer replay. |
| [V213](rows/V213.md) | RESTORED / B | Captureless canonical helper source binding, exact original adapters/extraction, complete Result/Option importer. |
| [V216](rows/V216.md) | RESTORED / A | Concrete bytewise 32-byte comparison source identity, unchanged extraction, complete Result/carrier law. |
| [V217](rows/V217.md) | SUSPENDED / D | Complete original checker provenance missing; 20 concrete range/index/fold records remain open. |
| [V218](rows/V218.md) | RESTORED / B | Concrete TrustedStep/Rev/usize laws, exact original adapter/extraction, full array writeback and carrier transport. |
| [V220](rows/V220.md) | SUSPENDED / D | Projection/pin tools are not a complete original checker; 20 concrete loop/index/fold/panic records remain open. |
| [V221](rows/V221.md) | RESTORED / C | zeroize 1.9.0 emitted byte/array dictionaries and explicit assembly-barrier source/world law. |
| [V222](rows/V222.md) | RESTORED / C | zeroize 1.9.0 scalar/Drop dictionaries, consumed execution and source-trace laws. |
| [V233](rows/V233.md) | SUSPENDED / D | Original Eager split checker passes; 61 raw-parts/offset/transmute/GenericArray representation records remain open. |
| [V236](rows/V236.md) | SUSPENDED / D | Original update/buffer checker passes; concrete BlockBuffer digest_blocks/slice-copy/index cone remains open. |
| [V237](rows/V237.md) | SUSPENDED / D | Original derived-default checker passes; concrete GenericArray builder/default-byte/initialization cone remains open. |
| [V246](rows/V246.md) | RESTORED / B | Original final-selector extraction;1.94.1 slice-loop, array equality and complete Result/carrier transport. |
| [V260](rows/V260.md) | SUSPENDED / D | Pin/association generator is not a complete original ordered-fold checker; 18 library records remain open. |
| [V265](rows/V265.md) | SUSPENDED / D | Original circle-control checker passes;M31::inv backend exposes 18 further library records;pointer Kani stays quarantined. |

All 100/100 Lean attempts were used: 85 passed and 15 failed. 71/120 capped native scopes; 0 Kani. Refusals are uncharged. Every run's exact target, status, wall time, peak RSS, swap, source revision and axiom output is in its receipt. All actual scopes used 6G high/8G max/swap0/Tasks64; Lean -M7000; all recorded swaps 0. No memory cap was raised.

[Combined audit41494](lean-41494/receipt.json), [complete-statement focused replay41495](lean-41495/receipt.json), [all 138-theorem axioms audit41496](lean-41496/receipt.json), and the [single final frozen manifest41499](lean-41499/receipt.json) pass. Only propext, Classical.choice and Quot.sound occur. [Final coherent fingerprint](resume-final-fingerprint.json): 69 private project modules and all 5,673 h4 external objects verified; [successful-source receipt association](resume-final-receipt-coherence.json). 517 frozen project files match. No external library or other job project object was rebuilt/substituted.

New finite validation includes 3,075 inverse cases each, 132 context comparisons, 806 statement comparisons, 128 Vec/two array take cases plus layout checks, 2,401 raw constructor pairs and 6,132 mixed iterator histories. Earlier deployed encoder/digest/points/zeroize/original-copy fixtures remain recorded and reused where their source/artifact did not change. Finite tests are not unbounded native or binary refinement. Failed raw elaborations/extractions and historical Kani qualifications remain visible and uncredited.

Endpoint premises removed 0, added 0, changed 0. E1/E2, native RunJoin/carrier/world composition, client proof-account route and L1/L2/L3 remain obligations. T stays exactly entropy_law, entropy_kernel, observation. The zeroize 1.9.0 effect law explicitly replaces SeqCst compiler_fence with an address-bearing readonly assembly barrier; [before/after and physical-observer limits](ZEROIZE190.md).

Two worker cooldown/sequencing violations and the historical per-attempt dependency-snapshot gap are recorded in [RESUME-SEQUENCING.md](RESUME-SEQUENCING.md). The final coherent DAG is an independent final measurement; it is not presented as a retroactive launch snapshot. Per-attempt dependency snapshots exist from41489 onward. The wrapper now enforces the 180s cooldown.

Stopping basis: Lean budget exhausted after final validation. The native budget is an upper bound; unchanged gates were not repeated to consume scopes. Nine rows retain the exact blockers above and in their JSON records. Five original executable full-body gates were recovered/replayed at the pinned source; extraction routes were rebuilt with their original selectors/adapters. Pin/projection/report generators were never relabelled complete checkers.

Next concrete deliverable: resolve V197’s pinned loan-validation obstruction without bypassing the guard, then bind its 1.94.1 range-index/TryInto-array/endian cone. Continue the other eight suspended rows from their explicit source/provenance blockers. [Own cache cleanup](resume-cleanup.json) preserves all source, LLBC, generated text, logs and receipts; no wallet/account keys were created or removed.
