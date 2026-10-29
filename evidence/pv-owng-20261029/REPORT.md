# D438 result after capacity relaunch

**V229 SUSPENDED -> SUSPENDED; V230 SUSPENDED -> SUSPENDED under own-1.**
No row restored; no witness-dependent FINDING. Privacy target not yet
established. Endpoint premises removed/added/changed=0/0/0.

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-own`, sparse checkout;
branch `codex/pv-owng-20261029`, base`4d2d31fa4f`. Read the complete prompt
chain, current pv-common including own-2'', proof/security rules, local/host
rules, prior ownf REPORT/STATIC-CHECK and this run's PLAN, commits, WIP snapshot
and receipts. No implementation source changed.

## Exact reason restoration is unavailable

The allocator is now cut at its entry points, including all its libc internals.
The earlier single-threaded and errno objections are withdrawn. Qualification
still fails **own-2''(a)'s no-foreign-call clause outside that black box**:
both original roots reach the legacy schedule's `endpoint_counts`; its two
1024-byte stack array initializations call `memset@GLIBC_2.2.5` at release
instructions`0x19b67` and`0x19b79` through GOT`0x5d240`.

[STATIC-CHECK.md](STATIC-CHECK.md) supplies the source locations, complete
root-to-witness chain, scope, checks and limits. This is a checked negative
qualification witness for the pinned original-root release cohort. It is
not evidence of witness-dependent behavior. No additional exception for libc
memory primitives is assumed. Under the inherited qualification-stop rule,
the positive own-2 route cannot be consumed; the own-1 binding remains open.

| Requested obligation | Disposition |
|---|---|
| own-2''(a), outside-box external reads and foreign calls | Conjunction rejected by explicit foreign calls; no positive purity certificate. |
| own-2''(b), address independence | Not certified for the complete cone. |
| own-2''(c), allocator-write channel closed | Not certified for the complete cone; internal errno reads are permitted. |
| Named explicit Result literals | No new theorem; inherited value lemmas retained without promotion. |
| One deployed-artifact execution per assigned function and literal byte equality | Not established. The existing execution is a diagnostic original-root probe, not the shipped client artifact. |
| Fingerprints | Measured diagnostically: rows`df394a5a8554d09c`, schedule`480809b836778dc6`; no proved Lean-literal cross-check. |
| Fixed allocation/order and abort | No new proof; allocator success/failure and abort remain under rdea-1. |

Evidence class **“exhaustive over a singleton input domain, deployed compiled
artifact” is NOT assigned**. No finite validation is promoted into a universal
native law or a source-binding proof. Diagnostic u16 payload hashes and exact
serialization limits appear in [diagnostic-values.json](diagnostic-values.json).

## Attempts and validation

Budget carried across the capacity error: **Lean0/60; capped native1/30;
Kani0**. The WIP snapshot contained one completed native scope, not zero;
no duplicate execution or unchanged rebuild was launched after relaunch.
No Env-J IDs used, including63797–63799. No Lean sources/declarations added;
combined formal audit/replay and #print axioms are N/A, not claimed successful.

The native scope compiled/linked the small optimized probe against existing
release rlibs, executed original roots, and captured disassembly/relocations.
It exited0, wall`0:00.25`, peak RSS118400KiB, swaps0, source revision
`1e0d4e741944be08ea7c2f1af88abedf3bc593ff`. Admission-before, launch and
in-scope barrier all say allowed:true. Caps6G/8G/swap0/Tasks64. Exact command,
features/profile, binary/input hashes, target, transport status and N/A axioms
are retained under [native-originals](native-originals/receipt.json) and
[native-result.json](native-result.json). The probe binary is not committed.

The new read-only checker exited0 at revision
`9a55f92d8909c5824a97489a74bab66df982e66a`, checking49 host files and six
tracked source blobs. Its wall time, source revision, checker/input hashes
and exact witnesses are in `static-capture.json`; stdout in `check-output.json`.
It launched no compiler, Lean process or requested root execution. Its peak
RSS/swap/axioms are N/A: it is inspection, not a formal release result.

## Retained obligations and next deliverable

T stays exactly entropy_law, entropy_kernel, observation. V370/D381/D386
compiler preservation and rdea-1 remain named. No dictionary, simulator,
observer, failure event, witness domain or endpoint signature changed.
No step adds a tool-trust reclassification. Earlier ownership/collector
work remains supporting evidence, including the uncompiled inherited
FocusedReplay, which is not consumed. V228/V239/V178 statuses unchanged.

The next concrete deliverable under the current rules is the own-1 source
instance: V229's actual initial endpoint-count arrays, mutable stores and
Result/world binding at tree242/246–263, followed by the remaining collector
stages and V230's usize/u16/stack-array binding. No new runtime exception or
silent evidence-class change is proposed as a proof of that obligation.

Only this task's tools/evidence paths changed. No crates/programs/protected
soundness files, keys, other worktrees or shared sources/objects were changed.
No cap raised, push, merge, full checkout or file over20MB. `git diff --check`
passes. Stage history is in COMMITS.txt; the final report commit follows it.
