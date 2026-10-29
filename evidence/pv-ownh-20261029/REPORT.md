# D439 result: V229 and V230 restored under own-2'''

**V229 SUSPENDED -> RESTORED. V230 SUSPENDED -> RESTORED.**
Exact evidence class for each:
**“exhaustive over a singleton input domain, deployed-configuration harness”.**
No disqualifying influence channel found. This restores these two native leaf
associations under the owner's D439 rule; it is not a source-binding proof.
**Privacy target not yet established.** No privacy-endpoint signature or
callback dictionary was edited; endpoint syntactic premises removed/added/
changed =0/0/0. The deployment obligations for these two leaf associations
are discharged by the permitted evidence class, with the boundaries below
retained. Lead integration/recount is still required.

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-own` (sparse);
branch `codex/pv-ownh-20261029`, candidate base `b7e35cda1b`.
`COMMITS.txt` gives `git log --oneline b7e35cda1b..HEAD` before this report
commit; the report was captured in snapshot `5f4d967a31`; the final handoff commit follows it. Only this task's evidence/tools and
new `PV_OWNH_` modules changed. No crates/programs, root checkout, other
worktrees, protected soundness files, keys, simulator, observer or T changed.
No release ELF rebuild was needed because implementation sources are unchanged.

## Requested obligations, in order

| Obligation | V229 | V230 |
| --- | --- | --- |
| D439 whole-cone classification | PASS | PASS, including V229 |
| Whole-cone address independence | Source argument plus checked base/offset algebra | Same, plus index/shift/array fold |
| Allocator-write channel(iii) | Closed | Closed |
| Named Result literal laws | v229_result; v229_selected; v229_selected_values | v230_result, composing complete row Result with14 named mask-chunk laws |
| Identical-source deployed-configuration execution | Exit0;214 words match all428 payload bytes | Exit0;64 words match all128 payload bytes |
| Allocation and abort | Fixed successful request sequence and every failure prefix; rdea-1 retained | Same, plus in-function row-buffer release; rdea-1 retained |

`STATIC-CHECK.md` gives the source argument, every stage, pointer case,
initialization/read set, panic/error/unwind treatment and channel(iii)
closure. `static-capture.json` pins44 complete source files and49 host inputs;
its compiled supporting frontier enumerates14 ordinary functions,74 call/jump
edges and63 RIP references, with no unclassified callee or mutable/TLS read
outside the retained boundaries. The source check covers inlining and
specialization as well as this frontier. The old memset objections are
withdrawn: they initialize caller stack memory and are permitted by D439(1).

The unlisted `__rust_no_alloc_shim_is_unstable_v2` is explicitly classified:
its selected body just returns, hence contributes no outside information.
Arithmetic/pointer intrinsics operate on constants or owned offsets. Panic
hooks are not called pure: local bounds, fixed-size iterator production and
u16 total ordering exclude ordinary panic edges; allocation failure/diagnostic
behavior stays under rdea-1. No wording-based stop or foreign-call blacklist
is used. The address proof is a source argument with Lean algebra, not a claim
that generic Nat pointer lemmas alone verify all Rust memory semantics.

The named laws are in
`docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OWNH_Literals.lean`.
The214-word literal is `PV_B3P_Sorted133.expected`; the64-word literal is
`PV_RDB2D_MaskChunk13.after`. The new results apply existing symbolic/named
schedule, sorted-value and mask-chunk laws; they do not reduce the whole
schedule/sort/fold in the kernel. V230's complete value-phase Result includes
the schedule error branch, which the named schedule theorem rules out.
CollectorProgram.complete/MasksWorld.complete separately retain allocation,
error/divergence and world effects. No success hypothesis was added to the
privacy endpoint. `ALLOCATION-ABORT.md` details exact request sizes/order,
drops and the distinction between V229's returned ownership and V230's drop.

## Harness, identity and bytes

`native-result.json` records rustc1.94.1, every resolved crate feature list,
release opt3, debug assertions and overflow checks off, panic unwind, exact
commands, lockfile identities and all input/binary hashes. The harness links
the reused pinned release statement rlib, hash
`0e0184bcafb0c970d9a2129429578f2fb85e69a844f6e4ddddafbb05f6f5acd0`,
from the prior recorded release compilation; it does not copy/rewrite either
root or replace the allocator. `crate-source-pins.json` verifies the entire
original statement crate (85 files) byte-for-byte against this branch.
Cargo metadata matches deployed feature units; lock resolution checks include
source and checksum, not merely version names. The harness driver reads its
mode/prints output outside the target functions' cones.

Harness SHA256:
`2501da70563c3695a97cd768a248c353d836e037050b99d5cef14176e74aca45`.
The native scope exited0, wall0:00.28, peak128764KiB, swaps0, source revision
`d2254d6cb1997283023cea2af72c5dcfb4835528`. Full capped/admitted receipt is
`native-harness/receipt.json`; all three admission decisions are allowed:true.
One direct execution per original root, then independent crate fingerprint
calls, ran in this one scope. No additional root execution was needed.

`byte-comparison.json` retains every expected byte and SHA256. Comparison
uses canonical semantic Result serialization: native exit0 is outer success,
Rust Ok tag00, LE u64 length, then every LE u16; no padding/pointers are read.

| Root | Full Result bytes | Payload SHA256 |
| --- | --- | --- |
| V229 |437 | c7bd261cac2b85895917f8ba9ddfa87345232c356d799de9e2ad855cf6a87b80 |
| V230 |137 | 49a9f8404c189c62111cb6a97d66769450210902f65c0861ec2df2a4cd845f04 |

Both runs cross-check the crate rows fingerprint `df394a5a8554d09c`.
Expanding all64 mask words into increasing row indices exactly reproduces
the214-word literal, and therefore the same independently computed FNV.
The crate schedule fingerprint is `480809b836778dc6`, matching the inherited
original-root cohort. That schedule hash is a diagnostic cross-check, not a
new Lean theorem about the schedule fingerprint. Exact output equality is
established by byte comparison, not inferred from hash equality.

## Attempts, audits and limitations

**57/60 Lean attempts:56 successful,1 failed; native1/30; Kani0.**
IDs63800–63853 and63897–63899 only. The initial range scan found no other-job
usage. Every compiler ran one module at a time through the standing run2
inside caps6G/8G/swap0/Tasks64, Lean-M7000. All launches satisfied exit0 plus
allowed:true before/in the scope; no refused/void attempt or cap increase.
Every receipt records target, source revision/blob/hash, dependency fingerprint,
exit, wall, RSS, swaps and complete axioms output. No host outage or gate wait.

The old RDB private cache was absent. We compiled the exact51 required
tracked dependencies privately rather than substitute sources or consume
stale objects. Preflight first inspected the broader historical cohort and
found an unrelated AspisR72Sampler object mismatch; sampler modules were
excluded from this task, not re-credited. Two subsequent inspection failures
identified missing private objects; no compiler had started. The successful
preflight verified5,673 external objects and105 remaining recorded EJR objects
before compilation. `cohort-verification.json` references the original
source/object authority; `final-object-fingerprint.json` rechecks every
consumed direct/transitive project import after the private rebuild.

Attempt63800 failed because `at` is a reserved identifier. The source was
changed to `position`, then63801 passed. No failed source was rerun unchanged.
All51 dependency compiles passed. Literal bridge63853 passed, wall0:04.06,
peak3152244KiB, the maximum across this job; swaps0. Final statement audit63897,
axioms audit63898 and single frozen manifest replay63899 all exited0.
`validation-summary.json` and `frozen-proof-manifest.json` record the precise
scope. The replay covers this focused value/resource closure, not the full
privacy endpoint. All17 new theorems use only subsets of
`propext, Classical.choice, Quot.sound`. No sorry/axiom/admit/native_decide,
XR imports, new resource-limit options or uncompiled declarations are consumed.

Retained: **V370/D381/D386** for crate-code -> shipped-binary codegen and
compiler/runtime memory primitives; **rdea-1** for allocator/resource/abort
adequacy and the public failure-event obligation. Existing Aeneas/Rust
semantic agreement remains a **reclassification within existing tool trust**;
no new Charon/Aeneas extraction or Kani evidence was introduced. T remains
exactly entropy_law, entropy_kernel, observation. No side-channel observer or
witness domain was weakened. The abandoned own-1 byte-memory route remains
supporting work, not the evidence class claimed here. V228/V239/V178 unchanged.

Next concrete deliverable: lead consumes these two restored native leaf
associations in the dictionary/deployment recount and coherent endpoint
closure. Nothing further is proposed as a prerequisite for the D439 leaf
restorations. No push/merge; no committed binaries/objects or file over20MB;
`git diff --check` passes. Rebuildable outputs created by this task are removed
after the final object fingerprint; inherited caches are retained unchanged.

## Capacity relaunch 1 finalization

Recovered snapshot `5f4d967a31` already contains the completed restoration,
all three final audits/replay receipts and this report. `resume-1.json` records
the independent receipt, source-hash, frozen-manifest and literal-byte checks
after relaunch; all passed. No new Lean or native run was required or launched.
Budget remains57/60 Lean,1/30 native scopes,0 Kani. The stopping condition is
completion of both requested leaf restorations; unused attempts are retained.
The final handoff commit changes evidence only.
