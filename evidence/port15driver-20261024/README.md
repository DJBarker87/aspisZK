# Port15DRIVER bounded handoff

Branch codex/cx-port15driver-20261024, base 21b33f3e7d. Plan/interface committed
first at 224a0010cb. **Whole-driver objective remains unproved.**

## Established

Accepted module `Port15DRIVER_TX1`, theorem `tx1`, checked at lean-019, states:
for every Ops/reserved/unwrap/rest/w, explicit `LocalBudgets rest w`, D/hash,
semantic/public/proof/H, actual `VTop_Flow.tx1 traceEffects D semantic pub proof
10#usize hash none` interpreted with `Port9OR_Installed.implementation ... rest`
has log length at most `(sites w).sum`, where the complete site sequence is

```
[0,w3,w4,0,0,w7,w12,0,0,0,0,477,0,w11,w10,w6,w9,3,0].
```

Thus its numerical expression is 480+w3+w4+w7+w12+w11+w10+w6+w9.
This is an all-outcome actual-source control proof. Each continuation uses its
actual typed return; fail/div and inner rejection retain only executed prefixes.
It includes literal batch0 once and writer once; pure lifted Results and library
calls require no success premise. Physical batch bodies are not normalized.
`Port15DRIVER_Cost.call/step/done` prove the structural log composition;
`Port15DRIVER_Local.delegated/library` expose the exact installed local bounds.

`LocalBudgets` is only
∀ {A} (op : Call A) H, operationId op ∈ [3,4,6,7,9,10,11,12,17,19] →
(eval H (rest op)).1.length ≤ w(operationId op).
No whole-driver acceptance, output equality, refinement or bound is hidden in it.
All argument quantifiers are unrestricted. Concrete rest/weights are uninstantiated.

## Incomplete target and retained failures

`lean-021/sources/Port15DRIVER_Driver.lean` is the final **failed candidate**, kept
outside the accepted Lean tree. TX2's declaration checked with standard axioms in
both lean-020 and lean-021, using the exact source tree and batch1/reader bounds.
Neither attempt is a green module receipt; no standalone TX2 artifact is claimed.
The complete TX2 site list is printed in those logs and in the candidate.

The `stages` proof exhausts the default 200000 heartbeats at whnf (lean-020 and
021). Attempt021 changes the proof by adding a symbolic done-tail log lemma;
that lemma checks with propext, but the composition still fails. This is an
elaboration failure, not a counterexample or memory failure. Dependent rust and
rust1161 contain compiler-generated sorryAx and are NOT accepted results.
Attempts003–018 preserve syntax, orchestration, context, and membership failures;
005 also retains a heartbeat timeout. No limit was raised. No failed input was
rerun unchanged. The unrestricted-rest 1162-ask/reject obstruction remains valid.

Next producer: with separately authorized budget, isolate explicitly typed
TX1/TX2 interpreted Program cuts and numerical length facts before applying the
bind lemma to Port1_Driver.stages; avoid definitional comparison of whole source
terms while elaborating bind bounds. Continue with same saved.deref, then rust,
then one successful full statement/hidden-premise/axiom audit. The target remains
1046+(2*w3+w4+2*w6+w7+2*w9+2*w10+2*w11+w12+w17+w19), and 1161 only if the
weighted sum ≤115. Neither full bound is established here. No optional accounting
bridge was attempted. Full final closure is not authorized.

## Validation and budget

New green focused modules: lean-001 Cost (exit0,1.996s,4434928KiB), lean-002
Local (exit0,2.248s,4445064KiB), lean-019 TX1 (exit0,3.623s,4454348KiB); zero
swaps, full axiom lists subsets of propext/Classical.choice/Quot.sound. Each
receipt retains exact command/target, source revision/hashes, selected dependency
object hashes, wall/RSS/swap and full axioms. These are focused cached checks,
not a coherent release rebuild. `source-audit.json` verifies accepted source
hashes, 21 receipts, all fresh complete-hierarchy admissions and 1050 reachable
local source hashes. Historical Port12 owned caps are reused with explicit source
assessment; no new ELF identity gate follows. Historical complete aggregate
coverage remains unverified.

Reviewed Port14 admission scanner/fixtures were copied to job-owned tools and
passed before the first launch: system/Docker coverage, hierarchical population,
nested cap deduplication, uncapped visibility, and missing-data failure. Every
launch used fresh admission under global lock and independently verified
6G/8G/no-swap/TasksMax64 scope limits. `source-audit.json` records every admission.

Inherited218 actual+1 preLean=219 charged; new21 actual=240/240, **zero remaining**.
Kani0/20. No allocation reset, local Lean/cold build, full manifest, runtime,
ELF/SBF, backend or extraction job. No shipped source/protocol/trust/contract/key
change; no keys touched; no merge/push.

Acceptance→recovery/parse/query/root/frame/no-hit, CleanAcceptedModel,
StoredCarrierBinding, concrete delegated source budgets and primitive adoption
remain independent open obligations. Both deployed targets not yet established.
Security bound unchanged: (Q+34)*B+kappa(Q+1161)+2^-126+2^-454.
