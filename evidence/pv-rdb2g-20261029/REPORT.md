# RDB2G — D440 exact-environment replay

**V256/V257 SUSPENDED. V231 unchanged: software path proved; SHA-NI path conditional on `R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics`, pending owner item 3. Privacy target not yet established.**

Branch `codex/pv-rdb2g-20261029`; base `0da960687bf9f66694b2fdb1fc2bd30f72586996`; exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-rdb2e`. Only replay orchestration and evidence under this directory changed. No Lean, Rust, production source or existing tool source edits; no new proofs, extraction, Kani or native regression; no push/merge or wallet/key activity.

## Exact environment and checked result

[Preflight](preflight.json) records JSON-equality to the original rdb2e Env-J environment: same Lean 4.32.0 executable hash/toolchain, external paths and literal LEAN_PATH, starting `/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/lean-objects`. The unchanged standing run2.py prepends that same object directory exactly as in the original command; its effective duplicated prefix is explicitly recorded. Sources stayed at their existing rdb2f source root, checked byte-for-byte against all 178 pinned blobs. All 5,673 external object hashes match. No shared source or other job directory was edited; the original rdb2e prefix is this explicitly authorized continuation.

40 modules were freshly elaborated in dependency order, all exit 0, with no source edits. This includes 30/30 original R72 closure targets and the additional prerequisites/consumers enumerated in [combined audit](combined-audit.json). Ninety unaffected canonical cache objects were verified with their source/import cohort and companions before staging at the original prefix. No affected cached object was reused. All successfully rebuilt direct dependency hashes match the recorded coherent cohort; [fingerprint](fingerprint.json.xz) freezes every object, source and external hash plus missing targets.

**Every one of the 40 rebuilt object hashes matches rdb2f; differences: 0.** R72 Funs is `ebeff6a2d06be7402afd468206e5542d15bea07d36b06f26412da992af0f052a` in both environments. Its source remains `b693c4bc5c00835a3f0fe3ff2b895ce58f40c6a52cf6cfdfdac7beacde8e000e`. The historical `38a9c51b…`/`5a4850e2…` mismatch is not a mathematical counterexample. The exact prefix change produced no byte difference in the completed targets; no claim is made about unrun targets.

## Budget and incomplete gates

The affected transitive graph has 49 targets: the original 30-module cone, 16 rdb2f consumers, and 3 audits. Host inventory additionally found 39 missing prerequisites from prior cleanup, with no matching surviving cache. The complete unchanged replay needs 88 first-pass attempts. Budget clarification was requested while continuing useful dependency-ordered work. No extension is inferred from elapsed time or silence.

The authorized 40 Lean attempts are exhausted; **48 exact targets remain**, listed in [comparison](comparison.json) and [plan](plan.json). Audits 63997–63999 remain unused. No audit was launched against missing or mismatched objects, and no restoration credit is granted from the partial replay. The original R72 closure gate alone passed; V256/V257 remain suspended on their uncompleted full consumer and audit gate. No theorem failure, admission refusal, timeout, memory kill or native-behavior finding occurred.

## AGENTS.md section 6 receipts and retained boundaries

Every attempt's exact target, source revision/blob/SHA, exit, wall, RSS, swap and full emitted `#print axioms` lines are in [combined-audit.json](combined-audit.json) and raw `lean-639xx/` receipts. Modules without an emitted axioms query receive no new aggregate-audit claim; prior rdb2f audits remain historical evidence only. Every emitted result uses only the permitted standard subset. Same-shell launch admission requires exit 0 plus allowed:true, followed by the standing in-scope barrier. Caps remain MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64, Lean-M7000; one module and one capped scope at a time.

Lean: 40/40 attempts, 40 exit0, peak RSS 3989348 KiB, swaps 0. Evidence/native scopes: 3/10; Kani0. Native differential suites were reused at their original finite-validation class, not rerun.

The exact original prefix is retained as a hash-pinned continuation cache for the remaining dependent work; no redundant source corpus, Cargo target, local build output or compiled binary is committed. This avoids repeating the cache-deletion failure that raised the replay cost. Sources and prior-job artifacts were not removed.

Endpoint premises removed0, added0, changed0. Inherited class-B structural (K-1 substitute) source laws remain under own-1, with compiler preservation V370/D381/D386 retained. Compiler/Aeneas/Rust agreement is reclassification within existing tool trust, never premise removal. T remains exactly entropy_law, entropy_kernel, observation. Runtime/allocator primitive adequacy under rdea-1, actual handlers, E1/E2, real RunJoin, proof-account routing and L1/L2/L3 retain their obligations. No privacy target claim.

Next: authorize the exact remaining attempt count, reuse the retained original-path objects, finish every listed consumer unchanged, then run statement audit63997, axioms audit63998 and focused replay63999 once. Restore V256/V257 only after those pass. V231 awaits owner item3 independently.
