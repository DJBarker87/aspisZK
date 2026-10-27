# RPx specialised replay handoff

**L187 is bookable for the specialised candidate `AspisR1.RPx_Deployed.deployed` on the pinned cohort. Its complete kernel statement is byte-identical to the reviewed `FJv_Deployed.deployed` statement.** No adoption is made by this job. The actual task top remains `AspisR1.FJv_Top.deployed` (83T/3P/13G); this replay removes zero premises. The deployed 100-bit target is not yet established.

Branch: `codex/cx-replay-deployed2-20261027`. Worktree: `/Users/dominic/ZK/.worktrees/cx-replay-deployed2`. Commits are local; no push.

## What was repaired

The lead correction authorizes repairing the ill-typed helper premise. `RPx_FIr_FinishComparison` maps the verifier observer with the existing `RPz7_PhaseIso.observerToFirst`, both in the finish premise and in the `S1SemanticFinishBounds.finish_success` call. Every original binder and the complete existential conclusion are preserved. `RPx_HELPER_CHANGES.md` records the complete before/after statements and the exact existing isomorphism laws; `RPx_helper.diff` isolates both edits. No new isomorphism or carrier equality is assumed. The direct consumer supplies `none`, whose mapped value is definitionally `none`.

Exactly the 36 blocked descendants are ported, consuming the repair transitively. Their declarations retain their namespaces and types so dependent carriers remain literal. Only the root namespace becomes `AspisR1.RPx_Deployed`. All files are new RPx_ files in this evidence directory; no existing source, session A candidate/worktree or other worker prefix is edited. `RPx_source-check.json` checks all 37 source deltas against the RPv snapshots: import redirection, the two helper edits and the root namespace change only.

## Statement gate

`RPx_statement-comparison.json` compares the complete untruncated kernel type emitted by fresh `RPx_DeployedAudit` to `evidence/stack1-20261027/FJv_after_deployed.kernel.lean.txt`. Both are 26452 bytes, SHA-256 `8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523`. No statement text is normalized. The historical descriptive comment is retained for whole-file comparison; the newly declared root name is reported separately. The quantified kernel-type payload is byte-identical independently of that comment. `RPx_Deployed.kernel-expr.json` retains the fresh raw expression and universe parameters.

The statement is unchanged from the specialised candidate reviewed in `HEADLINE-SPECIALISATION-DECISION-20261027.md`: its configuration specialisation and existing 83T/1P/13G statement are retained, not introduced or credited as new premise removals here. There is no minimal TOP statement change to report. Owner adoption remains a separate decision.

## Closure, axioms and formatter gates

All 37 source contexts compile; the root's actual header traverses 12712 modules including libraries. Every one of the 7040 historical planned contexts is present, plus the retained transport support `RPz7_PhaseIso`. No planned context is missing and no other replay context is added. `RPx_initial-closure-check.json` preserves the first postprocessor's detection of that support context; `RPx_import-closure-check.json` records the explicit 7041-context accounting. This was a reporting correction, with no compiler rerun or source substitution.

`RPx_0038` prints the root axioms `[propext, Classical.choice, Quot.sound]` (ordering varies in the structured traversal). All 180 formatter records are present and unreachable, including the tracked 84 actual formatter axioms. Formatter and write_str remain reachable library constants. This is root unreachability, not an import-wide standard-only claim. `RPx_formatter-records.json` records each result and the actual reachable axiom set.

`RPx_0039` audits all 105 declarations across all 37 fresh source contexts. Every structured axiom list matches its raw `#print axioms` report; there are no missing contexts/reports and no nonstandard axioms. See `RPx_declaration-audit.json`. Unchanged predecessor declaration audits are reused after object pin verification; this job does not rerun the package or predecessor proofs.

## Exact release records

| Target | Attempt | Exit | Wall s | Peak RSS KiB | Swaps | Source revision |
|---|---|---:|---:|---:|---:|---|
| RPx_FIr_FinishComparison | RPx_0001 | 0 | 3.058523621992208 | 3883524 | 0 | 3e44cc6712ebf61ecdeea1cc753f83670d5d51d0 |
| RPx_Deployed | RPx_0037 | 0 | 3.0538861809764057 | 5818596 | 0 | 35e31fabf4411c635164d2fd0c63a767e4176e7e |
| RPx_DeployedAudit | RPx_0038 | 0 | 15.053971160959918 | 6397372 | 0 | 4f3dbdc06e1ed3650152b03e8f920d886380b4e9 |
| RPx_DeclarationAudit | RPx_0039 | 0 | 8.34769582899753 | 5837920 | 0 | 4f3dbdc06e1ed3650152b03e8f920d886380b4e9 |

`RPx_attempts.jsonl` and each attempt directory retain exact command/target, source revision/SHA, dependency fingerprint, exit, wall, RSS, swap, cgroup limits and full axioms lines. Final usage is 39/150 Lean attempts, all pass; 0/0 Kani; compiler wall 131.69276512070792 s; maximum RSS 6397372 KiB; swaps 0; reservation retries 0. No timeout or memory kill occurred.

## Resources, seals and retained scope

One scope at a time in the existing pinned workspace; Lean 4.32.0, -j1 -M7000, MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64. Every admission requires reservation exit 0 AND JSON allowed=true before upload. No cap was raised. RPv/RPu/RPt/RPz8/RPz7 and both trusted overlays are reused; no predecessor object is overwritten or deleted.

Initial seal: all 6605 inherited paths match. Final seal: all 6730 paths match. Cleanup deletes only the two completed RPx query objects and their two overlay links; accepted source-context objects are retained for continuation. Post-cleanup seal: all 6726 retained paths match. See `RPx_seal.json`, `RPx_cleanup.json`, `RPx_post-cleanup-check.json` and `RPx_post-cleanup-pins.json`.

Two compile-free direct-dependency preflights failed because the copied job wrapper omitted RPv_overlay. The second ran after an unsuccessful local text replacement; no Lean ran for either. The search-path configuration was corrected; no host launcher or reservation infrastructure changed. `RPx_preflight0003.json` retains the diagnosis. These are not compiler attempts or failed-theorem retries.

No shipped Rust/cfg(kani), features, wire format, wallet/key or ELF changed. No Rust/Kani/SBF gate ran. The conditional ELF rebuild trigger did not fire. Inherited pins (not reproduced here): default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binary/object/ELF/archive is committed.

## Remaining obligations and next deliverable

No top assumption is removed, added or changed. The helper premise is repaired as explicitly recorded; every runtime, game, extraction, source/body association and trust premise of the reviewed top remains. The adopted frozen3/ARX game, RuntimePersistence and D188 trace-fidelity decisions are unchanged. This job does not establish source-to-ELF equivalence, D188-P2 associations/leaf bridges, L188, L154 or joint real-byte non-vacuity.

Next deliverable: the lead may book specialised L187 using this packet and resume the separate headline-specialisation adoption decision. The existing L187 booking for FJv_Top is unaffected. The deployed 100-bit target is not yet established.
