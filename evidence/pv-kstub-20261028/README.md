# Independent stubbed Kani re-verification — LOG D354 / D362

Target not yet established. Branch `codex/pv-kstub-20261028`; exact worktree `/Users/dominic/ZK/.worktrees/pv-relink`; candidate base `6d4350e42c6181924b80483f19fa6ccac5c3b4a7`. Recovery began at `03984c6b6e`; [RECOVERY.md](RECOVERY.md) and its JSON inventories list all 16 charged pre-crash runs, paired controls, the 51 status entries / 126 files, and the read-only recovery of K16. No unchanged harness was rerun.

Exact research KMX patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; exact stub SHA256 `ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138`. [Per-run audit](per-run-kmx-audit.json) checks immutable textual source snapshots. No new copy stub, crates/ or programs/ edit, push, wallet operation, release pin change or trust field was introduced.

| Row | Disposition | Reused finite native comparisons |
|---|---|---|
| V178 | stubbed Kani unconfirmed (timeouts) | 774,256 |
| V179 | stubbed Kani confirmed | 2,224,136 |
| V182 | stubbed Kani unconfirmed (timeouts) | 5,679,337 |
| V195 | stubbed Kani confirmed | 108,309 |
| V233 | stubbed Kani confirmed | 66,064 |

| Row / original root or window | Positive | Matched negative control | Credit |
|---|---|---|---|
| V178 / path_join8 | [K02](K02/receipt.json) TIMEOUT, 15:00.40 | [K30](K30/receipt.json) FAIL, 0:06.72 | none |
| V178 / join_one_byte | [K10](K10/receipt.json) TIMEOUT, 15:00.67 | [K11](K11/receipt.json) FAIL, 0:11.76 | none |
| V178 / join_two | [K16](K16/receipt.json) TIMEOUT, 15:00.71 | [K17](K17/receipt.json) FAIL, 0:02.85 | none |
| V178 / join_slices_two | [K20](K20/receipt.json) TIMEOUT, 15:01.28 | [K21](K21/receipt.json) FAIL, 0:03.64 | none |
| V179 / string_ascii8 | [K04](K04/receipt.json) PASS, 4:50.58 | [K05](K05/receipt.json) FAIL, 1:22.28 | confirmed |
| V179 / string_scalar | [K06](K06/receipt.json) PASS, 2:03.41 | [K07](K07/receipt.json) FAIL, 0:07.41 | confirmed |
| V179 / string_path | [K12](K12/receipt.json) PASS, 0:11.47 | [K13](K13/receipt.json) FAIL, 0:11.02 | confirmed |
| V182 / push_ascii1 | [K08](K08/receipt.json) PASS, 1:44.32 | [K09](K09/receipt.json) FAIL, 0:03.87 | confirmed |
| V182 / string_push | [K14](K14/receipt.json) PASS, 4:12.00 | [K15](K15/receipt.json) FAIL, 0:21.00 | confirmed |
| V182 / push_bytes | [K18](K18/receipt.json) TIMEOUT, 15:01.31 | [K19](K19/receipt.json) FAIL, 0:06.92 | none |
| V195 / wide_flat | [K22](K22/receipt.json) PASS, 0:05.08 | [K23](K23/receipt.json) FAIL, 0:01.13 | confirmed |
| V195 / all_carriers | [K24](K24/receipt.json) PASS, 0:06.29 | [K25](K25/receipt.json) FAIL, 0:05.85 | confirmed |
| V233 / split64_coordinate_lo | [K26](K26/receipt.json) PASS, 1:19.06 | [K27](K27/receipt.json) FAIL, 0:05.22 | confirmed |
| V233 / split64_coordinate_hi | [K28](K28/receipt.json) PASS, 1:15.00 | [K29](K29/receipt.json) FAIL, 0:06.76 | confirmed |

Every credited positive has a matched failing control. [control-source-audit.json](control-source-audit.json) verifies the exact fixture substitutions and final Eq-to-Ne change, identical bound/stub attributes, one failed check, and the concrete false expectation. Three terse logs use a runtime-formatted assertion-panic placeholder; their attribution comes from this frozen-source audit, rather than literal inequality text in the log. All other runtime checks remain unchanged. A timeout earns no credit. K01 was cancelled after an ambiguous selector; K02/K03/K10/K16 retain their historical timeout evidence. K30 replaces only K03's timed-out symbolic negative with a concrete admitted changing-output fixture, and never repeats its unchanged source. Complete per-window and per-run statuses are in [table.json](table.json).

The index 165 String append gate performs exactly one actual append at symbolic prefix length n<=2 and symbolic tail length m<=1, over arbitrary admitted UTF8 bytes. `n=2,m=1` recovers its original domain; [symbolic-append.json](symbolic-append.json) retains exact before/after source. The other historical fixed-domain append gates retain their original bodies; index 165 is strengthened as recorded. V233 uses length windows n<=64 and 64<n<=129, each retaining every output coordinate; the Lean frame/coverage law composes them only when both runtime windows succeed.

No completed positive disagrees with the prior structural bindings or reused same-input native differentials unless explicitly labelled a finding in table.json. Those native checks remain finite validation, never a universal runtime proof. Structural evidence remains labelled `structural (K-1 substitute)`; [comparison-inputs.json](comparison-inputs.json) records the precise prior scopes and residuals. [observer-pattern-audit.json](observer-pattern-audit.json) records no targeted observation-cut Option assumed None; ordinary get(i) comparisons permit None outside the range without assuming it. The reported NBZ_K042 finding changes no credits here.

The exact KMX value law, copy-window/frame transports, symbolic append specialization, prefix/tail/optional-coordinate bridge and split metadata/byte coverage are model theorems. They neither prove a timed-out native gate nor establish allocator success, arbitrary representations, compiler refinement, source-image or deployed association. All existing complete-Result source laws remain unchanged.

Privacy endpoint premises: removed 0, added 0, changed 0. Before and after, the canonical privacy endpoint retains its existing deployment/refinement/observer obligations; the capped trust list is exactly entropy_law, entropy_kernel, observation. No simulator or observer was weakened.

Validation: 30/30 charged Kani invocations; 10/10 Lean attempts. Every admitted scope uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one own scope at a time. Kani uses CPU 0–3, optimized Cargo, exact root selection and unwinding assertions. Recovery refusals are uncharged, wait at least 180s and retry the same unlaunched name; transient transport/scan races retain their prescribed retry histories. The historical 7.513s cooldown shortfall and initial selector cancellation remain recorded in operating-notes.json and recovery evidence. [recovery-operating-notes.json](recovery-operating-notes.json) also records one source-only SCP upload without a fresh pretransfer admission receipt; it launched no compiler or solver. Receipts record target, exit, wall, GNU-time peak RSS, swap and revision; timeout RSS can omit killed solver descendants and is not presented as full aggregate memory.

Focused attempt 44706 failed because prefix is a reserved Lean keyword; [lean-parser-correction.json](lean-parser-correction.json) records the corrected-source replacement at 44707 and combination of related optional-coordinate laws into the same module. The failed draft receives no proof credit; no unchanged compile was rerun. There are 9 successful Lean attempts and 1 focused parser failure.
The final private manifest is run once after its focused prerequisites and bridges. Exact axioms and formal resource receipts are retained under IDs 44700, 44701, 44703–44710 (44702 was already used by another job and was skipped before any own compile) and audited by [validation.json](validation.json). Existing endpoint/deployment residuals remain. The next concrete deliverable for any unconfirmed row is a smaller controlled runtime window or a faithful extracted native proof, followed by the affected bridge; no unchanged timeout is pending a retry.

Final formal target `PV_KStub_Final` ([44710 receipt](44710/receipt.json)): exit0, wall0:00.25, peak RSS751160KiB, swaps0; source revision `ab3e1a6e6c15d6a45fd296b0ca48b948323be6e6`, source SHA256 `6cd1ad05da67e6f086c9db8badebeecad29e280e909f0bfa722ecb28b248af9b`. All20 printed theorem axiom lists are subsets of propext, Classical.choice, Quot.sound. [cleanup.json](cleanup.json) retains object SHA256/size and confirms no live own proof process and removal of owned rebuildable caches. Budgets are exhausted; no unchanged replay remains pending.
