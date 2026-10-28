# Deployed class-B row repair — resumed final report

**Ten rows RESTORED at their existing qualified library/source-law boundaries. V178 and V181 stop with checked obstructions to complete Result/effect association with their old references. Privacy target not yet established.**

Branch `codex/pv-rdb1-20261028`; exact assigned worktree `/Users/dominic/ZK/.worktrees/pv-rdb1` retained. Base `6273e6206164ac60fbc68a49fa888f98b87476f1`. Host `/home/dombarker/project-offloads/codex-pv-rdb1-20261028/`. No push, implementation edit, ELF rebuild, key creation or key cleanup. Shared rulings and host-restoration flag were read. [Commit history](COMMITS.txt) records `git log --oneline 6273e6206164ac60fbc68a49fa888f98b87476f1..HEAD` through the source/row commits; the final report/receipt commit follows that snapshot.

The previous report was stale at relaunch: the WIP snapshot already contained 40 Lean attempts and 36 native scopes, including eight additional restored rows. All launched attempts were recovered and counted; no job was resubmitted merely to recover its receipt. This continuation used three more Lean attempts and eight more native scopes.

## Restored rows

All restoration credit is **structural (K-1 substitute)**. Each linked row record retains its original closing theorem, before/after statement, source gate, proof receipts, finite validation, configuration and remaining semantic boundary. These are source-association repairs, not new security endpoint proofs.

| Row | Proved deployed law and complete binding |
|---|---|
| [V164](rows/V164.json) | Complete compressor/index-loop binding; arbitrary complete-Result arithmetic operations retain order and errors; deployed pointer construction laws |
| [V170](rows/V170.json) | Deployed Vec<u32>/Global destructor slice construction, initialized prefix, no payload destructor, capacity-zero bypass and exact deallocation/world effects |
| [V182](rows/V182.json) | Byte append: fresh iterator view, reserve/growth guards, capacity, snapshot copy, error-before-copy, length update and allocator/private world |
| [V183](rows/V183.json) | Deployed Layout::repeat padding-mask identity for actual Rust element layouts; complete reserve allocation/reallocation/error and physical/private effects |
| [V184](rows/V184.json) | Sized NonNull cast; last-slot offset/bounds; generic non-Copy/ZST pop ownership and unchanged allocation/memory/frame |
| [V186](rows/V186.json) | Default and owned reference share exactly Vec::new at the same generic instantiation; zero live length gives empty value without changing ZST capacity |
| [V187](rows/V187.json) | Forward iterator count/ZST cursor and array initialization; generic owned Vec-to-array complete Result, input retention on mismatch and finalization effects |
| [V195](rows/V195.json) | All eight four-byte serializer chunks covered once, complete copy result/frame, transparent ManuallyDrop borrow/restoration and excluded bounds panics |
| [V198](rows/V198.json) | All four writer copies and ordered range checks; complete return and buffer effects, including first eight bytes retained on second-range panic |
| [V219](rows/V219.json) | Complete boundary traversal/index enumeration and independent four-limb updates, with arbitrary complete-Result arithmetic |

For these rows the same original model/callback qualifications remain. New private model embeddings and pointer/copy/layout lemmas connect the changed deployed source shapes. Returning constructors and operations are not promoted to unconditional allocation success. Raw allocator/reallocator, language intrinsic, valid runtime carrier, compiler/executable and side-channel obligations remain at their recorded original boundaries.

## Checked obstructions and restated laws

**[V181](rows/V181.json): capacity Result mismatch.** On deployed 64-bit Linux, `String::with_capacity(9223372036854775808)` panics before allocation. The old `string_capacity_reference` is `String::new()` and returns empty. [Native witness](result-effect-witness/output.log) and [complete deployed constructor gate](v181-deployed-binding.json) record this discrepancy. `PV_RDB1_V181Finding.overflow_world` proves the overflow result leaves the allocator world unchanged; `no_unbounded_promotion` excludes equality with the unconditional returning model.

The repaired safe reference is `String::new(); reserve_exact(n); return value`. `PV_RDB1_V181.complete` and `with_handlers` prove its complete allocation/error/world law, including zero request, layout overflow, null allocation/private state and actual error handling. [1,027 native pairs](v181-capacity-native/receipt.json) validate headers and deterministic overflow paths finitely. The selected all-Usize `ok empty` callback remains unchanged. Its historical bounded/returning-value qualification is not refuted; an unqualified native Result association is unavailable. Stop this row pending a reachable-domain/error-aware endpoint adapter.

**[V178](rows/V178.json): path allocation effects differ.** For base `base` and absolute path `/`, native `Path::join` first clones the four-byte base, then clears and reuses that buffer. The old reference skips the clone and requests eight bytes for its fresh output. Returned contents agree; allocation requests differ. The [native witness](result-effect-witness/output.log) records both requests. The historical gate explicitly retained allocation effects as residual, so this is an obstruction to discharging that residual, not a refutation of its narrower contents theorem or evidence of a Rust version regression.

The [deployed path gate](v178-deployed-binding.json) checks the full `_push`, clone chain, Unix separator/prefix selection and changed truncate chain. `PV_RDB1_V178.truncate_complete` proves zero-length u8 truncation preserves address/capacity/world. `join_repaired` proves the clone-first reference equality for arbitrary complete-Result clone/append operations; `clone_failure` preserves failure before append. Sixty-four repaired-reference value/allocation-event pairs pass finitely. Stop this row pending transport of the clone-first error/world law through its endpoint adapter. No old world-equality credit is invented.

## Validation, provenance and budget

Deployed configuration: `tools/r1-cost-probe`, client `devnet_spend`, features `r1p-check,aspis-r1-cost-probe/ct-host-prover`, rustc **1.94.1**, release opt3, assertions/overflow checks off, panic unwind. [Resolved features](resolved-features.json) retain every crate and effective profile in the 487-unit graph. Each scope receipt references that configuration; std-only fixtures separately record that no feature-bearing project dependency is linked. Changed library bodies are checked against installed pinned 1.94.1 rust-src.

Earlier finite validation is reused: u32 drops260; path pairs774,256; append pairs5,679,337; reserve pairs2,160 including failures/overflow/ZST; pop99 plus33 Drop-bearing ZST; array606 plus99 ZST; serializer108,309; writer4,101; compressor768/boundary128 and supporting polynomial128. These remain finite checks. No quarantined or copy-dependent Kani PASS is re-credited; Kani usage is zero.

All 5,673 external objects were reverified before the final compile. Own import source/blob/object hashes are recorded recursively. [Final source manifest](final-source-manifest.json) matches165 checked body-file hashes across12 row bindings. The earlier172 project-file and2,048 attributed sysroot checks remain recorded separately.

Combined statement/axioms audit **54738** passed. Focused replay of all ten restored rows **54739** passed with their full original quantifiers and Result/world conclusions. Only `propext`, `Classical.choice`, `Quot.sound` occur. Replay54799 failed because the new wrapper supplied unapplied theorem functions beneath local binders; applying those functions is the recorded source change compiled successfully at54739. Every final PV_RDB1 module has an exact-source successful receipt; failed elaborations remain evidence, not credited proofs. No unchanged full regression was repeated.

Totals: **43/100 Lean attempts, 44/120 capped native scopes, 0/0 Kani**. Remaining57 Lean IDs are54740–54796; remaining native scopes76. All swaps zero. Peak Lean RSS2,666,280 KiB; peak native RSS571,616 KiB. Six failed native/preflight source gates are retained with their corrected-input successors; none is a behaviour verdict. No memory kill, timeout, refusal, cap increase or transport failure occurred. Full targets, exits, wall/RSS/swap, source revisions and axiom lines appear in receipts and [audit.json](audit.json).

The unused budget is not reported as exhaustion: all ten nonfinding rows are finished; the other two stop on the checked Result/effect discrepancies above. No row stops merely at an unwritten pointer/allocation law.

## Premise accounting and next deliverable

Removed: the deployed native-to-owned-reference source-association obligations for V164,V170,V182,V183,V184,V186,V187,V195,V198,V219 at their existing qualified source/library boundaries. Retained: V178/V181 complete Result/effect association, endpoint E1/E2, real RunJoin, client route, compiler/executable and runtime/allocator primitive adequacy, and L1/L2/L3. No dictionary, simulator or observer was edited; T remains exactly entropy_law, entropy_kernel, observation. No new trust item, success premise or narrower native input domain is silently introduced.

Next concrete deliverable: error/world-aware endpoint adapters consuming the proved V181 reserve-based constructor and V178 clone-first reference, followed by endpoint dependency replay and premise audit. `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` is **not established** by this repair.

[Final cleanup](cleanup-final.json) hashes three retained-at-run-time ELF fixtures before deleting only those executables and this job's143MiB Cargo target cache. Sources, receipts and shared Lean objects remain. No key was created, accessed or removed.
