# P2Prime actual-root handoff

Status: focused root closure; complete release target not yet established.
Branch `codex/cx-p2prime-20261026`. Only P2P_ modules and this evidence directory
change; local commits only, no push or merge.

## Established claim

`AspisR1.P2P_Top.deployed` replaces the actual Rc6 root's L097/L098 proof/public
binding guards with the SINGLE measured account collision alternative. The
binding-dependent acceptance, nonrejecting and caller continuation are unguarded
in its good branch. Unconditional native source/cuts/run/TX2/encoding/parser/P6/
checkpoint/history/copy/physical-event outputs remain on the same witnesses.

## Statement change and accounting

Before: actual `Rc6_Top.deployed` retains P2Prime inside CPP_Acceptance,
Rc5_Nonvacuity and Rc6_Caller. Its two atomic laws are L097/L098.
After: `P2P_Result.Outcome` retains every unconditional field and adds the
literal collision event OR those three consequences with the guards removed.
`P2P_Projection.good` preserves the witnesses outside that event;
`P2P_Forget.forget` then returns the complete original Rc6 result.
Full source/elaborated statements are retained in P2P_BEFORE_STATEMENT.lean.txt,
P2P_AFTER_STATEMENT.lean.txt and P2P_EXPANDED_STATEMENTS.txt.

The former arbitrary analysis selector is instantiated by
`P2P_NativeSelection.pair`, a deterministic function of the installed SDK,
e1/e2, data2 and slot, fixed before H. The attacker programs, input buffers,
query budgets, decoder, byte prover, runtime, extraction relation, native
acceptances and approved game clauses are unchanged. No account/native-output
association assumption is added. The recorder's four audit reads may select
any such fixed bytes; source-derived cuts and original validator/op22 observations
prove these are exactly the native writer/reader bytes. P2P_Origin.Fact is a
DERIVED output carried through the original source factory, never a new premise.

The event in P2P_Result is exactly the event whose indicator is integrated by
F3T_AccountCharge.mass in this top's numerical conclusion, with the SAME
account source/project/selector. P2P_Accounting.single_event checks this boundary.
1921 source reads +1040 replay +4 complete-byte reads =2965. The loss stays
6*(Q+2965)^2/2^256, charged ONCE; union overshoot0, no new summand.
No global hash injectivity or collision-freedom premise is used.

F3X's separate candidate is not imported. Rc6's raw frozen3 canonical join
and runtime StoredCarrierBinding remain explicit. A future composition must
use this exact selected event or prove transport to it; equality with a
differently selected recorder is not claimed by this handoff.

## Recount and non-vacuity

The P2P_recount.py ledger method removes L097/L098 only. Actual antecedents:
83T+32P ->83T+30P; excluding eleven approved game leaves:83T+21P ->83T+19P.
Deployment only6T+8P and aliases0T+2P are unchanged. Deduplicated total:
89T+40P ->89T+38P; all retained audit rows89T+42P ->89T+40P. C=0 throughout.
No trust item, input law, attacker restriction or metric is added. The conclusion
change and analysis-projection specialization are explicit; this is charged
binding, not unconditional collision-free byte identity. Full reviewed mappings,
structure comparisons and every retained row are in P2P_premises.json.
The authoritative ledger is not edited because this job may touch only its prefix.

P2P_NativeNonvacuity.accepted_input returns the SAME actual source-cut public/
proof bytes, a physical1880-byte accepted input and a proof excluding an always-
rejecting driver in the good branch. P2P_Nonvacuity.exists_clean separately
constructs a clean oracle world under the zero-adversary-read budget. Neither
claims a single joint accepted cryptographic fixture of all retained runtime,
source/extraction and frozen3 laws. That full release fixture remains open.

## Freeze and remaining release work

No shipped or cfg(kani) file changed; the three-ELF rebuild trigger did not fire.
Inherited, not newly reproduced pins:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Session A worktrees/candidates and parallel worker prefixes were untouched.
No wallet/key/account/fund/authority operation, toolchain change, native build,
Kani run, package replay or frozen-manifest regression occurred. RuntimePersistence,
SDK/std/allocator/entry/syscall trust and the native extraction/source-to-artifact
boundary remain within their original scopes. L157/L159 and other workers' rows
are retained; no closure credit for their candidate results. L186 lowering,
L187 coherent frozen dependency replay and L188 final release trust/axiom audit
remain. Focused standard-axiom compilation is not those release gates.

## Validation and stopping condition

Budget exhausted:100/100 Lean actual invocations, 95 passing and5 excluded development failures;0/10 Kani. Prior interrupted run used027; resume used028-100. Every current one of95 P2P modules matches an exact-source passing receipt and host source/object pin. All new top theorem axioms are printed.37 fresh kernel inventories compare43 unchanged retained structures.

Root058: target P2P_Top.lean; exit0; wall4.269139587006066s; peakRSS5454864KiB; swap0; source revision6721cc03d95d86eadc1eac21c4608bcabad006ac, dirty tree with exact source SHA256 4ada6712404cd2cc4fe9b144136050febf04ab5a09926d79680d1a81ac403047. #print axioms deployed:[propext,Classical.choice,Quot.sound].

Final100: target P2P_AuditAxioms.lean; exit0; wall3.295200233987998s; peakRSS5422864KiB; swap0; revisionc45c6a02e286f1415b1f4e87b35badc53cb58831, exact snapshot retained. All printed axioms are standard-only. Total measured Lean wall350.95354386407416s; peak5454864KiB; swap0 throughout.

All jobs used one admitted scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and Lean-j1-M7000-DElab.async=false. No time/memory kill, unchanged timeout rerun, raised cap, package replay or infrastructure repair. Per-attempt receipts retain exact commands, revisions/source/dependency hashes, stdout/axioms, cgroup values and all resource measurements. Failed sorryAx recovery prints are excluded. The initial capacity interruption left no failed Lean job to rerun. P2P_ATTEMPTS.jsonl indexes every receipt.

P2P_validate.py and P2P_recount.py pass. P2P_HOST_PINS.json compares95 own sources/objects and249 selected dependency objects with zero mismatches. Coherent SInt2 objects and unchanged host launchers were reused; this is focused cached composition. Source/script/document diff checks pass. All proof attempts are now stopped at the100-attempt budget.

Local stage log before final evidence commit:

```text
c45c6a02e2 Verify clean-branch transport and native accepted-input non-vacuity
5486a52f45 Remove native pair binding guards under the single charged account event
6721cc03d9 Preserve native byte origins through the Rc6 source construction
7d5c60a40a WIP snapshot before capacity relaunch (auto 0)
ff7acd4071 Prove single-event byte binding and explicit source-pair transport
4b95bfa6ed Record P2Prime input freeze and collision association obligations
```
