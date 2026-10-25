# RawJ handoff — budget exhausted; L157 remains open

Branch `codex/cx-raw-join-20261026`. No push. **Target not yet established.**
**Ledger premises removed: NONE. L157 canonicalJoin.verifier and its L182
actual-dictionary instance remain OPEN. L159 was excluded and untouched.**
Stop:100/100 charged Lean attempts;99 actual invocations plus own-prerequisite
prelaunch007;0 Kani. No checked counterexample against shipped source.

## Checked result and before/after

`RawJ_FramedAccepted.accepted_pair_unified` (099) retains all
`GExq_FinalAccepted.accepted_pair_unified` hypothesis binders and conclusions
on the same full f/s/cuts/outer/pre/middle/fs/ss. It adds the actual response
records, exact containing CallerRecord same-world evaluation, and all three
original C1/C2/row30 frame occurrences on that ordered oracle log. The frame
conclusion is universally conditional on a parse of the SAME f.proof bytes;
that parse is not added to the endpoint's hypotheses. See
`lean/RawJ_FramedAccepted.lean`, `RawJ_before-after.json`, and stage2/3 notes.

`RawJ_FirstTraceFields`/`SecondTraceFields` invert original accepted source
runs and construct the canonical owner's full FirstCut/SecondCut records.
`RawJ_Scheduled` equates their log with the native schedule by deterministic
run equality. D189, Claims, TX1/TX2 and both source-program conclusions carry
those same witnesses throughout. No independently existential second cut,
chosen accepting log or extra successful native call is supplied.

`RawJ_PrepareSemantic` exposes the actual semantic child and original prepare
continuation. C1/C2 source reads are identified with returned roots via
originalNew_static and the actual semantic return, then with the original
proof's parsed committed roots using physical root binding. `RawJ_OriginalFrames`
transports them into the complete original-account CallerRecord log. Native
transport is success-conditioned; rejected prefixes are retained by the
separate all-world experiment envelope.

## Account query count and exact numerical check

`RawJ_AccountBudget.budget` establishes the NEW complete adaptive
`GExq_AccountExperiment.program` envelope **Q0+Q1+1921** on every H and every
outcome. It is proved through the actual containing owned callers,
polymorphic child calls, allocation/copy/cleanup wrappers and adaptive second
choice. Preprocessing Q0 and adaptive Q1 remain explicit uniform adversary
bounds; Q1 ranges over first input, saved bytes, post heap and final allocator
state. No native acceptance or syscall-totality hypothesis is used for this
all-world count. The inner1921 bound was not transferred without proof.

`RawJ_CollisionBudget.replay_collision` additionally charges ALL1040 canonical
replay reads. The account experiment's collision upper bound is

    6*(Q0+Q1+2961)^2 / 2^256.

`RawJ_Numeric` checks the denominator and a conservative EndP-style accounting
sum retaining its original1161 collision term and both aborts. At Q0+Q1=0,
the exact spare margin is

    2^-108 - 6*(1161^2+2961^2)/2^256 - 2^-126 - 2^-454 > 0.

There is no numerical shortfall or target relaxation. This is checked
arithmetic and an account collision bound, **not** an established account
security endpoint or an equality with EndP_Headline's source experiment.

## Remaining blocker and next concrete deliverable

The complete adaptive account program still needs the restricted(Q+34) start
charge, transport of its original accepted frames/canonical replay into the
actual byte-indexed Port1 interpreter, and the strict all-H ordered-log
equality consumed by L157. A collision-or-recovery alternative does not give
strict equality in collision worlds. Those obligations were not silently
replaced by a no-collision hypothesis, arbitrary runtime, or new trust item.
The next theorem must consume `RawJ_FramedAccepted` and the independently
proved account envelope on the same deployed interpretation and establish the
restricted start count and charged replay/Port1 transport. Runtime history
and stored carrier binding remain outside this task's L157-only scope.

No security/trust assumption was added, removed or weakened. Existing SDK,
TrustedStd, runtime admissions, extraction/digest/syscall and child-cone
boundaries remain. No joint accepted fixture inhabiting all retained native/
runtime/crypto premises is claimed. Pure adapter slots remain inherited
dictionary operations, not freshly certified physical helpers.

## Validation, resource limits and freeze

`RawJ_final-audit.json` maps all60 current prefix modules to exact-source
exit0 receipts.100 charged attempts =99 Lean invocations (60 successful,
39 development failures) +one own-dependency prelaunch007. No missing
unchanged dependency build was needed. All invocations used existing unchanged
S2W launchers in coherent SInt2, one module,-j1,-M7000,-DElab.async=false,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. PeakRSS at most
5352504KiB; every swap count0. No OS wall-time timeout or memory kill.
Heartbeat failures066/069 were structurally isolated into opaque bodies,
explicit binders and a small pure error-map lemma; no unchanged timed-out
rerun or raised resource/depth/heartbeat cap. Failed Lean recovery sorryAx
prints are excluded from accepted evidence.

Final `RawJ_Audit.lean` /100: exit0,wall1.8554694670019671s,
peakRSS5245564KiB,swap0,revision anchor
e0089898bc59d4ca8bdad86e1e65848f36a2570e with the audit source dirty
and exact SHA snapshot. All14 main audit prints use only
[propext,Classical.choice,Quot.sound]. Every other new top theorem has its
own successful axioms print. Receipts retain exact target/command/sourceSHA/
revision/dependency-object fingerprints,exit,wall,RSS,swap,cgroup,axioms/errors
and source snapshots. No source contains sorry/admit/axiom/native_decide or
depth/heartbeat overrides. Source-only git diff --check passes. The complete branch check reports
two retained trailing-whitespace lines in failed attempt022/063 stdout; raw
evidence is preserved unchanged (RawJ_diff-check.txt).

This is focused verification against pinned reused objects, not a fresh
release/package/frozen-manifest replay. `RawJ_reused-source-sha256.txt` matches
every reused GExp_/GExq_ host source with the local source; per-invocation
receipts pin directly selected objects/sidecars. The original SInt2 workspace
and immutable candidate provenance remain as documented by inherited handoffs.
No launcher/monitor/cache dependency or other worker's source was changed.
Final scope inventory has no RawJ job; another worker's NP6 scope was left alone.

No shipped or cfg(kani) source changed; ELF rebuild trigger did not fire.
Inherited pins, NOT newly rebuilt/revalidated:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No Kani,Rust,SBF,package replay,keys,funds,ELFs,binaries,objects,archives,global
ledger or other-cone candidates changed. Only RawJ_ modules and this receipt
directory changed. Stage commits are local and were not pushed.
