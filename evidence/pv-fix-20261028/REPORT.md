# D423 V213 compliance resume

**V213 OPEN. Focused restoring-theorem statement/axioms audit PASSED (62113).**
The restoring theorem is freshly compiled, but the requested complete consumer
closure remains unfinished: 17 modules require compilation after the 40-attempt
budget was exhausted. This is partial restoration evidence, not completed V213
restoration or a privacy-target result.

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-fix` (sparse), branch
`codex/pv-fix-20261028`, resumed at `9fb7df1043928e6d79a1034305ffe6ef445822d9`.
Host workspace `/home/dombarker/project-offloads/codex-pv-fix-20261028/` retained.
No sparse expansion, source/proof changes, new proofs, native scopes, Kani,
implementation changes, trust items, or wallet/key operations. No push.
D422 history and its original report remain available at the resume base.

## Item (1): exact result and unchanged statements

The invalid historical binding attempt 41466 remains VOID. The compliant binding,
Funs and Exact objects from 62012–62014 were reused after recursive verification,
without recompiling them. The eight affected modules and original source pins
remain exactly those in `affected-order.json`.

62100–62111 rebuilt the missing canonical/Op107/Option/shift prerequisite chain
in dependency order, using the exact pinned git blobs. 62112 then recompiled
`R1Z.PV_RDCD_Op109Audit` (blob `a7065373e002744da36da2627b99b2e27f18cd6d`).
62113 ran the pre-existing, unchanged inspection-only `PV_FIX_V213Audit.lean`.
Its full output is `out-62113.log`. It checks and prints:

```lean
R1Z.PV_RDCD_Op109Audit.source :
  ∀ [ProverRwFull.ExternalTypes] (ops : ProverRwFull.ExternalFuns)
    (x : ProverRwFull.aspis_core.field.wide_exact.WideExact),
    ProverRwFull.ExternalFuns.op109 x = do
      let value ←
        PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv
          (R1Z.PV_CB_Op109Transport.encodeW x)
      Aeneas.Std.Result.ok
        (Option.map R1Z.PV_CB_Op109Transport.decodeW value)
```

The statement covers the complete Result/Option, with no canonical-input
restriction. Its ExternalTypes and ExternalFuns parameters remain. The printed
proof is the application of `PV_CB_Op109Exact.op109_source`. All three audited
theorems (`source`, `reference_equation`, `op109_source`) report exactly
`[propext, Classical.choice, Quot.sound]` (universe parameters retained in raw logs).
No theorem statement, hypothesis, proof text or source blob changed.

62114–62139 rebuilt another 26 unchanged prerequisites of the remaining aggregate
consumers. **FinalAudit, FinalReplay, AllAxioms and FinalManifest have not been
recompiled here.** Therefore V213 is OPEN despite the successful focused audit.
The exact remaining dependency order is:

- `R1Z.PV_RDCD_EmptyRaw194`
- `R1Z.PV_RDCD_ConstructorFrame`
- `R1Z.PV_RDCD_EmptyRawRepeat`
- `R1Z.PV_CB_Op118Types`
- `R1Z.PV_CB_Op118Funs`
- `R1Z.PV_CB_Op118Transport`
- `R1Z.PV_CB_Op118Arrays`
- `R1Z.PV_CB_Op118Exact`
- `R1Z.PV_RDCD_Range194`
- `R1Z.PV_RDCD_PointsStep`
- `R1Z.PV_RDCD_Op118Audit`
- `R1Z.PV_RDCD_RangeForward`
- `R1Z.PV_RDCD_FinalAudit`
- `R1Z.PV_RDCD_Replay`
- `R1Z.PV_RDCD_FinalReplay`
- `R1Z.PV_RDCD_AllAxioms`
- `R1Z.PV_RDCD_FinalManifest`

Next deliverable: retain this private cache; rebuild these 17 unchanged modules
in order under compliant admission, ending with the pinned FinalManifest. The
focused audit 62113 is already green and need not be repeated unchanged unless
its inputs change. No source elaboration failure occurred in D423.

## Admission, cache provenance, and receipts

Exactly **40 Lean compiler attempts, 62100–62139: 40 PASS, 0 FAIL**; zero native
scopes, zero Kani, zero reservation refusals, zero new ruling (t) violations.
Each launch checks admission in the same Python invocation as the scope, requiring
exit 0 and `allowed:true`; the in-scope barrier checks admission and actual limits
again. The job-wide 180-second cooldown guard remained active; no refusal triggered
it. `resume-driver.py` runs each scope to completion before the next launch.
No ID outside 62100–62199 was used; `resume-id-scan.json` scans other privacy-job
receipt names and shared sent records before launch.

Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean -M7000, -j1, timeout 900. Maximum RSS was 3,289,628 KiB; all swaps were zero.
Source revision for all attempts was `4d9da5e481` (full hash in
`resume-revision.txt`), with each individual source blob and SHA256 recorded.
The driver and final evidence scripts are retained in this evidence commit;
this is not a claim that every wrapper file was committed at compile time.

`resume-external-check.json` verifies all 5,673 external primary objects against
the inherited coherent replay authority before the first compiler. The external
manifest itself retains its original authority chain. The unchanged toolchain
and effective LEAN_PATH are retained in `resume-env.json` and every `env-621*.json`.
`resume-cache-check.json` verifies the source hash, object hash, and complete
import closure of 13 reusable project objects, including 62012–62014. For fresh
objects each launch checks the recorded actual import hashes, recursively,
against the objects it will load. Unverified fallback objects are rejected.

The retained-cache search found 47 candidates in other Stream B private object
directories, including 18 byte matches to historical objects. None was reused:
every historical byte match had a missing/differing import closure against the
current verified cohort. The search and exact closure gaps are retained in
`resume-retained-cache-search.json` and `resume-retained-cache-assessment.json`.
No other job's directory or shared object was modified.

`resume-final-check.py` verified admissions, actual cgroup limits, exact sources,
environments, output hashes, standard axiom lists and all consumed project import
edges. `resume-final-fingerprint.json` retains the verified 51-project consumed
closure; this is not the unfinished final-manifest closure. Exact source pin/HEAD
checks for all 69 project sources plus the existing audit wrapper are recorded in
`resume-local-verification.json`. Cached objects and source snapshots are retained
on the host for the next dependent targets.

Full commands, dependency fingerprints, exit, wall, RSS, swap, revision and full
axioms output are recorded in `resume-attempts.json`, plus raw
`receipt/admission/barrier/env/out/time-621*.{json,log}` files. “No output” below
means the unchanged target contains no emitted axiom directive; it is not a claim
of axiom freedom.

| ID | Target (`R1Z.` prefix) | Exit | Wall | Peak RSS KiB | Swap | #print axioms |
|---|---|---:|---:|---:|---:|---|
|62100|`PV_RDCD_CanonicalSource`|0|0:03.82|2637824|0|1 standard reports|
|62101|`PV_CB_Op107Types`|0|0:01.20|2634600|0|No output|
|62102|`PV_CB_Op107Funs`|0|0:01.48|2652588|0|No output|
|62103|`PV_CB_Op107Transport`|0|0:01.25|2633796|0|No output|
|62104|`PV_CB_Op107Exact`|0|0:01.30|2640672|0|1 standard reports|
|62105|`PV_RDCD_Option194`|0|0:01.27|2631820|0|No output|
|62106|`PV_RDCD_OptionBinding`|0|0:01.17|2634944|0|1 standard reports|
|62107|`PV_RDCD_Wrapping194`|0|0:01.20|2633332|0|2 standard reports|
|62108|`PV_RDCD_ShiftLiterals`|0|0:01.18|2628024|0|4 standard reports|
|62109|`PV_RDCD_Cast194`|0|0:01.21|2629900|0|2 standard reports|
|62110|`PV_RDCD_Op107Audit`|0|0:01.18|2636924|0|5 standard reports|
|62111|`PV_RDCD_ShiftBound`|0|0:01.25|2628408|0|1 standard reports|
|62112|`PV_RDCD_Op109Audit`|0|0:01.14|2637032|0|3 standard reports|
|62113|`PV_FIX_V213Audit`|0|0:01.18|2631248|0|3 standard reports|
|62114|`ProverRwFullFuns`|0|0:23.52|3289628|0|No output|
|62115|`PV_RDCD_ZeroWorld`|0|0:00.47|700048|0|2 standard reports|
|62116|`PV_RDCD_ZeroSelected`|0|0:01.89|2659548|0|9 standard reports|
|62117|`PV_RDCD_ZeroConsumed`|0|0:01.24|2641148|0|4 standard reports|
|62118|`PV_RDCD_ZeroDrop`|0|0:01.36|2643612|0|2 standard reports|
|62119|`PV_RDCD_ZeroCursor`|0|0:00.34|694660|0|3 standard reports|
|62120|`PV_RDCD_ZeroTrace`|0|0:00.32|695136|0|3 standard reports|
|62121|`PV_RDCD_ZeroCompatibility`|0|0:00.36|696604|0|3 standard reports|
|62122|`PV_RDCD_Audit`|0|0:01.22|2641784|0|9 standard reports|
|62123|`PV_RDCD_V216Raw`|0|0:01.27|2642904|0|No output|
|62124|`PV_RDCD_ByteArray`|0|0:01.27|2630412|0|2 standard reports|
|62125|`PV_RDCD_ContextTotal`|0|0:01.25|2631920|0|1 standard reports|
|62126|`PV_RDCD_ContextInstall`|0|0:01.29|2644836|0|5 standard reports|
|62127|`PV_RDCD_V246Raw`|0|0:01.29|2649600|0|No output|
|62128|`PV_CB_Op229Types`|0|0:01.22|2638736|0|No output|
|62129|`PV_CB_Op229Funs`|0|0:01.37|2637704|0|No output|
|62130|`PV_RDCD_Slice194`|0|0:01.48|2644916|0|3 standard reports|
|62131|`PV_RDCD_SliceArrayBinding`|0|0:01.40|2634120|0|2 standard reports|
|62132|`PV_RDCD_StatementBridge`|0|0:01.94|2630204|0|3 standard reports|
|62133|`PV_RDCD_GenericArrayEq`|0|0:01.93|2634764|0|3 standard reports|
|62134|`PV_RDCD_Index194`|0|0:01.23|2640504|0|2 standard reports|
|62135|`PV_RDCD_V169Raw`|0|0:01.19|2631372|0|No output|
|62136|`PV_RDCD_Defaults194`|0|0:01.32|2637868|0|5 standard reports|
|62137|`PV_CB_TakeRef`|0|0:01.25|2630788|0|No output|
|62138|`PV_RDCD_TakeBinding`|0|0:01.38|2643916|0|7 standard reports|
|62139|`PV_RDCD_CpopLiteral`|0|0:01.37|2634368|0|3 standard reports|

## Item (2) and remaining privacy obligations

**Replay PASSED (62002), unchanged and not rerun.** D423 did not touch its source,
objects, wrapper, receipts or prior evidence. Its historical input failures 62000
and 62001 remain recorded in `attempts.json` and the D422 report at `9fb7df1043`.

No headline premise was removed, added, or changed. E1/E2, real RunJoin/native
carrier/world, proof-account client routing, L1/L2/L3, compiler/primitive adequacy,
and T exactly `entropy_law/entropy_kernel/observation` remain. V213's complete
restoration credit remains OPEN because its four aggregate consumers and their
missing prerequisites have not been recompiled. The privacy target is not yet
established. No ELF rebuild was required because no implementation changed.

Commits are path-limited to this evidence directory. `COMMITS.txt` records the
resume preparation; obtain the final report commit with
`git log --oneline 9fb7df1043..HEAD`. No push performed.
