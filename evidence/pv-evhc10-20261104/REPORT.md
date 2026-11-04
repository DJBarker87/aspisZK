D596: all three steps PASS in the single authorized agg16 scope `pv-evhc-92080.scope`.

Worktree `/Users/dominic/ZK/.worktrees/pv-evhc`, branch `codex/pv-evhc-20261029`, audited source revision `74ac46dbcac0643157cf9c90b1fcb212212513cb`. ID 92080 consumed; 92081–92089 unused by this job. No retry of a Lean step, no cap change, no audited source change, and no repeat manifest replay.

| Step | Exact target | Exit | Wall seconds | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 | PV_BR_FixtureConsumer | 0 | 4.560968301 | 8812388 | 0 |
| 2 | PV_NER_Scan full combined import closure | 0 | 54.118269247 | 12374496 | 0 |
| 3 | NEP_Driver final, all 32 roots | 0 | 92.571466069 | 12424428 | 0 |

Whole runner: exit 0, wall 160.604783654 seconds, peak RSS 12424428 KiB, swaps 0. Runner-recorded cgroup memory peak: 3498364928 bytes. The RSS and cgroup fields are preserved verbatim from the host measurements. Limits: MemoryHigh 14G, MemoryMax 16G, MemorySwapMax 0, TasksMax 64; Lean -j1 -M15000 -DElab.async=false. Each step had the unchanged 600-second timeout.

Before admission, 33,254 object/companion/runner pins passed, including the entire combined object manifest, the 16,058-module NER cohort and its companions, and every NER_REBUILT_OBJECT_PINS entry. Committed input hashes, full lead runner hashes, and the compiled walker pin were checked. Admission check 0 returned exit 0 and allowed:true. See PREFLIGHT.json, COMMITTED-INPUT-PINS.json, admission-92080-0.json, and admission-status-0.json. The unchanged complete object pin table is retained in agg-92080/ALL-OBJECT-HASH-CHECKS.json and the runner source snapshot.

The command was exactly the READY-AGG.md AGG-SEQUENCE.py invocation, with the unchanged D595 driver and byte-identical research walker. Every consumed input and DRIVER.diff was snapshotted under lean-92080/sources/evhc10-92080; receipt.json records their hashes. AGG-SEQUENCE rechecked the object pins before step 1 inside the same scope.

Step 2 scanned exactly 16,539 modules, 1,593,937 declarations and 39,863,671 edges: zero dangling references, all imports matching. Full scan rows are in agg-92080/COMBINED-SCAN-ROWS.jsonl.

Step 3 completed all 32 roots, including every privacy root, with zero unresolved constants. Every walked axiom set is a subset of Classical.choice, Quot.sound, propext, and equals collectAxioms. Both soundness results exactly match NER_AXIOMS.json:

| Root | Reachable constants | Edges scanned | Axioms |
| --- | ---: | ---: | --- |
| AspisR1.RPx_Deployed.deployed | 115256 | 5743676 | Classical.choice, Quot.sound, propext |
| AspisR1.NDR_CombinedAudit.sourceOnHeadline | 885736 | 15048019 | Classical.choice, Quot.sound, propext |

Complete raw results and full summary-based #print axioms output are retained in agg-92080/step-3.log and RAW-AXIOMS.json. Full reachable lists for all 32 roots are retained losslessly under reachable/, each with its original SHA-256 and a manifest. validate_receipts.py independently checks all lists, raw results, scan rows, source snapshots, resources and admission. RECEIPT-VALIDATION.json records PASS.

Pre-admission input corrections are recorded in INPUT-CORRECTIONS.json and PRE-ADMISSION-INPUT-STOP.json. No admission or Lean attempt preceded those corrections. The prior evhc8 authorization was restored byte-for-byte before the controller ran; POST-RUN-HOST.log confirms its retained hash. No evhc8 output receipt was overwritten.

Composition audit counts: all three required steps passed. No privacy premise was removed, added or changed. FixturePdaRuntime base, event-acquisition and joint-simulation obligations remain. The fixture witness does not prove the event-acquisition or joint-simulation links. The privacy target is not yet established. This run establishes closure coherence and the specified dependency/axiom audit, without claiming discharge of the endpoint's hypotheses.
