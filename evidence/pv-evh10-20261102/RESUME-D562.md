# D562 context checkpoint — exact adopted raw backend and native error receipts

Resume base8791a69cd673ce0429229e606d5356f87876e951, same worktree/branch.
Target NOT established. Rows removed NONE; T unchanged. This is a context
checkpoint, not budget exhaustion, external blockage or a shipped counterexample.

## Exact adopted backend confirmation

adopted_backend.py binds the exact committed D474(C) client-build.json and
client-unit-graph.json, pinned to the inspected bundle revision. Binary SHA256
is da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0.
The receipt selects getrandom_backend="linux_raw", rustc1.94.1 Linux x86_64,
getrandom0.3.4, client profile opt3/panic abort/no debug assertions/no overflow
checks. LinuxRawControl uses that direct syscall control, not dlsym.
Inherited native-sources.json uses a later user_client recipe; this new receipt
checks the exact adopted devnet_spend binary separately. Neither binary code
preservation nor non-MSAN artifact/kernel association is inferred from flags.

## New checked native error frontier

NativeRawReceipt.error_receipts connects the original extracted entropy error
iteration at opsNative (per-reached-world op129 selection) with:
- source Result projection and reached valid error code;
- deployed zeroize1.9.0 cleanup and heap coherence;
- every raw request confined to original64 and separated from heap/old live
  stack bytes, deriving request separation from ORIGINAL admission;
- a continuous private before/after buffer and OS-world chain into delivery;
- exact events = ordered existing per-call events ++ deployed cleanup events;
- all previous live stack owners AND their bytes preserved.

No private buffer becomes a public payload. Retired slots can reuse addresses;
the new byte-preservation law deliberately covers LIVE slots only. It does not
claim erasure/preservation of moved-from copies or compiler spill/register state.

LinuxRawFrame.consumed_prefix additionally proves consumed bytes survive later
short reads/EINTR under its explicit per-call KernelFrame memory law. This law
is STILL P for the actual kernel; it was not folded into entropy_kernel density.
See getrandom-frame-laws.json for exact modules/attempts and retained premises.

Original address/source/native frame association, HeapSeparate/LiveSeparate,
initial HeapCoherent, actual syscall ABI/memory association, successful inner32
continuation, advancing-world dictionary and complete native entry remain P.
Fresh ghost identity does not prove numeric address separation. No endpoint
premise was removed by wrapping it into an invariant.

## Source frame and diagnostic findings

frame_source.py records the complete original generate_for_mask_nonce body.
Ordinary entropy error drops only original64; both inner32 are uninitialized
at that point. Success MOVES both32 into returned Self and drops original64.
Do not invent zeroization of moved-from stack copies. Retry increments then
scope drop order is leaf32,field32,original64. L3/V370 retains copy residues.

LiteralWriteAll consumes the existing accepted stateful WriteAll.Driver.
New error/zero branch laws retain ErrorKind inspection, interrupted-error drop,
WriteZero construction, world updates and every prefix. StderrWrite adds the
actual inspected StderrRaw EBADF wrapper and ordinary guard-release ordering.
Classification/drop/lock primitives stay explicit Q operations. The connected
LiteralDiagnostics.Writer still requires actual native primitive association.
No Aeneas core::fmt always-Ok law is used for diagnostics.

ClientOverflow.no_success excludes successful source values on every modeled
hook/abort outcome. source_failure_retained proves that a hook's Aeneas source
failure HAS a source projection. A draft blanket no_source claim was false and
corrected before compilation. Therefore one cannot install unconditional old
PartialView capacity transport for this arbitrary writer. Do not hide writer
failure behind a successful domain or reclassify it as a native fault.

diagnostic-write-source.json retains inspected std1.94.1 bodies. The remaining
FileDesc/libc/errno, io::Error representation/drop, guard/reentrancy/borrow,
Box/hook/environment/backtrace/profile and allocator association is P. This is
local source-control fidelity, not complete native diagnostic fidelity.

## Failures and corrections

79546: ambiguous raw loop unfolding; qualified name in79548.
79548: uninferred successor buffer/world in have; supplied them in79549 PASS.
79555: missing NativeRawSpatial import; corrected79556 PASS.
79558: abandoned simplified writer draft failed empty/control syntax. Replacement
uses the inherited stateful Driver rather than pure classifier/construction.
79559: ambiguous writer loop; qualified in79560.
79560/61: missing Except error carrier in continuation; explicit carrier79562.
No unchanged failed retry, memory kill, cap increase, timeout or swap.

Local commit45b61bb625 temporarily overwrote accepted PV_EVH_WriteAll by name.
Stage rejected its source SHA before any SSH staging/compiler/ID consumption.
169cf3617b restores the exact accepted bytes and creates a DISTINCT module;
all later stages verify every accepted source hash again. Full correction is
writeall-name-correction.json. No accepted object was replaced or recompiled.
The final LiteralWriteAll is an extension of the inherited Driver, not that
abandoned simplified loop. Source-only frame inventory initially matched the
early nonce guard's identical error string; fbc628700e selects the final error.

79552 had TWO uncharged admission refusals. Each was followed by the full180s
cooldown and retry on SAME unlaunched ID; retry2 passed. Refusal histories and
all original summaries remain. No marker/reservation/launcher change.

## Next work

Discharge original physical frame/source interpretation and actual raw syscall
association, then inner32 success/retry/drop and advancing source family. Keep
new private receipts through full native/L3 work. Complete real allocator type
metadata/padding/RawVec/Global/System ValidAnswer/owned Vec interpretation,
actual stderr primitive/guard/io::Error/hook fidelity, seven callback runtime
installations and all remaining source leaves/full entry. Only AFTER that prove
actual-family oraclePrefix/countTrace/nonce-store fileTrace links and (v-prime)
reduction to successful ACTUAL worldRun at opsNative AND allocator world.
D520/U/D524 inputs, NativeObstruction62/op132 and all deployment/privacy rows
remain. No MODEL witness, extra trust item or blanket FinishedView shortcut.

## Final accounting for this context checkpoint

Charged79545–79564:20 attempts,12 accepted/8 failed. Cumulative83/100,
55 accepted/28 failed. **17 REMAIN; NEXT FRESH79565.** Both audit triplets
79397–79399 and79597–79599 untouched. No pending submitted/refused compile,
no WIP Lean source; accepted bytes immutable. StderrWrite79563 failed because
`scoped` is reserved Lean syntax; renamed withGuards,79564 passed. Every new
accepted theorem prints only standard axioms (or none).

New peak4,465,004KiB; slowest12.79s. Cumulative peak remains4,616,200KiB.
All runs used retained cohort, same admission guard, one6G/8G/swap0/tasks64
scope and Lean-M7000. No timeout/kill/swap/cap rise, native/Kani/new extraction,
release replay, push/delegation, crates/programs/soundness edit, other-worktree
write or keys/accounts/funds action. Native closure preflight remains required
to FAIL. See validation.json/host-final.json for final read-only reconciliation.
