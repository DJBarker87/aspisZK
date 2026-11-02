# D543 final handoff — gates incomplete, native budget exhausted

Exact worktree `/Users/dominic/ZK/.worktrees/pv-uc`, branch `codex/pv-uc-20261029`, base `683e01efee`. Only writer. Read original prompt-pv-uc.txt, pv-common through current rulings, root AGENTS, local-lean and recovered historical r1p-common; source/read provenance retained. Final [REPORT.md](REPORT.md), [gate-status.json](gate-status.json), [attempts.json](attempts.json), [EXTRACTION-BLOCKERS.md](EXTRACTION-BLOCKERS.md) give results and exact blockers.

## No own work is running; never resubmit N75145

The SAME N75145 finished exit 0, scope inactive. **1,000/1,000 passing pairs**, 500 transfer + 500 withdrawal, **2,000 real optimized prover calls**, no mismatch. Wall 5:32:32, max process RSS 608,728 KiB, cgroup peak 2,234,355,712 bytes, swap 0, no OOM/task-limit event. `native75145/{receipt,completion-status}.json` and `final-gates/differential/{summary,comparisons}.json` reconcile every pair ID. The old local collector was gone; recovery was read-only after waiting, never a resubmission. Read-only monitor session 36779 / functions cell 38 completed. Earlier host-checkpoint/differential-snapshot records are historical, not a pending run. No private corpus duplicate/download: proofs, recovery records and ledgers remain on host.

## Scope and ID accounting

**50/50 native scopes complete, 0 remain. 6/40 Lean attempts used, 34 remain. Zero Kani. No pending own scope.** IDs native75100–75147 plus native75149/75150 are charged. native75148 is retired but UNCHARGED: quiet pre-admission refusal before any capped scope or sample. Next unused IDs: **N75151 (NO NATIVE BUDGET)**, **75006**. Never reuse any ID, even refusals. Do not launch another timing run: the single admitted D543 rerun has been used.

All scopes used normal shared admission (exit 0 AND allowed:true), 6G high / 8G max / swap 0 / TasksMax64; Lean -M7000, own sequential scopes. Reservation refusal requires full 180-second cooldown, retired ID and next unused ID. No shared launcher/tool infrastructure changed, no cap raised, no unchanged failed source resubmitted. Own wrappers stage committed own inputs only AFTER recorded initial admission and verify hashes. Keep pinned caches and all key/recovery material.

## Formal results and hard blockers

- **75000 PASS:** verbatim focused decoder Types.
- **75001 FAIL:** verbatim decoder Funs at line 80: `U64.wrapping_shl i5 32#i32` supplies I32 where the authoritative library requires U32. This reached elaboration; failed-source SHA guard forbids unchanged resubmission. No generated body/library shim was installed. Prepared emitted decoder execution is NOT RUN because this prerequisite fails.
- **75002 FAIL (pre-elaboration dependency):** full-entry Types cannot find `PVUCEntry.TypesExternal.olean`. Original 25 type + 119 operation axiom templates remain UNINSTALLED; do not fabricate a compile by filling them with axioms/sorry/stand-ins. No full-entry Types/Funs object exists.
- **75003 PASS:** two negative model diagnostics, `PV_UC_FormattingObstruction.fdArguments_equal` and `no_faithful_fd_formatter`. Final Rust wallet.rs:42 formats `/proc/self/fd/{fd}`; current builtin Arguments/new_display erases fd before external alloc.fmt.format. Native **N75147** confirms distinct FD3/FD4 paths using the exact reached expression on optimized Rust 1.94.1. Observable JSON printing reaches the same erasure mechanism. This is a checked model obstruction, not a formatter source law, privacy closure or D525 wire mismatch. Do not weaken fmt-1, use Unit as writer evidence, or edit extractor/generated semantics/library objects to bypass it.
- **75004 PASS:** namespace-only copy of adopted NDP raw-walk source, provenance in raw-audit-provenance.json.
- **75005 PASS:** final focused raw audit of both negative theorems plus Wallet type. Raw types/values graph = collectAxioms = #print axioms = exactly propext/Classical.choice/Quot.sound. Reachable counts 2045/2106/1996, 3938-module root closures, loaded/serialized axiom inventories checked. Imported nonstandard library axioms are inventoried and unreachable from these roots. `final-gates/axioms/validation.json` and validate-axioms.py independently validate inventories/DAGs/printed sets. **Full entry and decoder Funs are NOT audited. No cold/full closure replay ran.**

h4 manifest SHA d9187c80... and all 5673 external objects are verified before every compile with the first-root rule; lean-object-authority-check.json records it. Successful own object hashes/source hashes are verified and reused. No library object rebuilt/substituted and no other stream's project objects loaded. Source/std/feature/native associations remain P obligations, not new T items.

## Timing and final native scopes

- **N75146 FAIL before compilation:** own diagnostic PATH lacked rustc. **N75147 PASS** with corrected absolute installed-tool path, using the SAME retained partial directory and exact source expression. Both receipts retained; changed input recorded.
- **N75148 refused before admission:** foreign `pv-b3p6-lean-79728.scope` appeared after earlier quiet read. No scope/sample; ID retired; full 180-second cooldown observed.
- **N75149 INVALID:** the ONE admitted D543 D359(A) rerun. Pre-admission load 0.605/1.553/5.547, no other capped jobs. Foreign capped Lean `run-r8cdd4a24c6c447139f14433d5ebdc3e2.scope` appeared during first transfer pair; post-call guard stopped. **Zero accepted complete pairs.** Retained unaccepted calls: baseline 12.909407617 s, candidate 13.285308944 s. No accepted ratio, median or performance pass. `final-gates/timing-d543/` retains each call before post-check, binary pins, all quiet/load and marker records. Previous invalid N75143 remains. No combined-client timing repeated; shared marker never edited or bypassed.
- **N75150 PASS:** last native scope, checksum-only final binding. All **31/31 hashes** match: production source/manifest/lock inputs, user/fixture/audit executables, 3 frozen release ELFs, original full-entry emission/templates. `final-gates/final-audit.json`. This does not turn incomplete formal/timing gates into a pass.

## Frozen source/artifacts and next concrete deliverable

D543 changes no production Rust. Final app source still last changed in 11b19c589e. User SHA **9310ca5e3dcb3b2e8d7ac51312d6737aa465d2f8321fdaef6928114ffa38538e**, 2,029,480 bytes; exact locked/offline Rust 1.94.1 linux_raw client-profile recipe in final-build.json. Fixture SHA **6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194**, unchanged from N75121; fixture source byte-identical to base, crates/programs unchanged. All three ELFs passed N75137/38/39; native decoder instruction trace passed N75140 (63 instructions, zero/ff/ramp, decoded values and retained record checked). Those unchanged successful gates were not rebuilt/replayed. Do not claim historical bundle binary identity.

Next deliverable: source-faithful handling of shift/formatting operands under the unchanged accepted extractor, faithful external bindings, then full-entry compilation and actual-closure audit/replay. A new source/artifact requires covered-gate reassessment. Valid D359(A) still requires an actual protected quiet period and additional authorization/budget; no remaining native scope or rerun allowance exists here. Unspent Lean budget cannot justify installing arbitrary extern definitions or resubmitting unchanged failed output.

No ledger row or endpoint hypothesis removed, added, weakened or changed. T remains entropy_law, entropy_kernel, observation. Retain E1/E2, V370/V371, real RunJoin, native I/O/JSON/hash/formatting association and whole-client L1/L2/L3. **Privacy target not established.**

Never read/touch retained deployment authority keys. All gates offline except SSH transport; no RPC/devnet/broadcast, key cleanup, merge, push or repin. All task keys, recovery files, nonce ledgers, fixture SBF keypairs and continuation caches remain retained. Final report commit follows the COMMITS.txt snapshot.
