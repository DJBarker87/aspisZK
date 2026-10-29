# LOG D377 resume handoff — 2026-10-28

Exact worktree `/Users/dominic/ZK/.worktrees/pv-b3p6`; branch
`codex/pv-b3p6-20261028`; resume base `1e826627aa39fe02569bf840efb894eaa287efcf`.
Final Lean proof revision `49557de942ec32710ff035d5d396f30b77056472`.
Stage history: [COMMIT-LOG-resume3.txt](COMMIT-LOG-resume3.txt).
Prior handoff: [FINAL-D373.md](FINAL-D373.md).

**V228 newly closed; V229 and V243 retain their accepted closed status.
V241, V245 and V244 remain open. Target not yet established.**

Stop: all 100 Lean attempts consumed, IDs51900–51999 exactly, 65 successful
compiles and35 failed drafts; zero Kani. Capacity relaunch inherited89 charged
attempts, not a fresh budget; the final11 contained10 successful compiles and
one failed draft. Refusals at51948 and51985 were uncharged and retried at the
same IDs after cooldown. Failed drafts and their sorryAx placeholders earn
zero proof credit. No checked counterexample to ROWS7 or the endpoint was found.
Historical12 Kani runs remain spent/uncredited; no copy-dependent or
function-pointer Kani PASS is newly credited.

|Row/op|Status and exact scope|Next deliverable|
|---|---|---|
|V228/132|CLOSED selected callback/source/value requirement, **structural (K-1 substitute)**. Whole nested-loop ordered-value/count law, exact3803-cell capacity, source predicates, native binding, original carrier installation and261 other-field frames.|Separate-budget KMX re-verification when required; whole native composition remains substantive.|
|V229/133|CLOSED, inherited accepted structural packet.|No repeated full regression.|
|V243/226|CLOSED, inherited accepted structural packet.|No repeated full regression.|
|V241/224|OPEN. Both extracted component loops have complete Result laws and checked mutable-restoration fidelity. No whole native root or installed callback closure.|Convert prefix/suffix field and row types explicitly, connect original trace and registry, prove whole structural/reference law and install op224 with nonvacuity.|
|V245/228|OPEN; not advanced.|Owned registry reference and full structural/reference law.|
|V244/227|OPEN; not advanced.|Owned field-arithmetic reference and plain structural binding; no chained-field Kani.|

## V228 closure

[V228 closure](V228-CLOSURE-resume3.md) and
[structural packet](structural132-resume3.json) record21 exact native body/helper
pins, deployed feature parity, every representation/control difference and its
named Lean transport law. `MaskScan132.inner`, `MaskOuter132.outer`,
`MaskCapacity132.full_count` and `MaskOrdered132.complete_result` prove the
whole loop, without normalizing a1024-row recurrence. `MaskSource132.native_free`
and `MaskFreeLaw132.free_eq` connect source helper predicates. `Install132.reference`,
`value_law`, `count_law` and `nonvacuity` install the reference in the original
carrier. This is a structural source argument, not compiler correctness or a
Lean theorem of native machine execution.

Exact-feature native validation compares statement, copy, deployed host array
and reference on the same unit input and all3803 ordered cells. It is **finite
validation**. Receipt `receipts-resume3/native132-resume3-exact/receipt/receipt.json`:
exit0,26.752s,peak508860KiB,swap0,source0ed3bce74f,axioms N/A.

## V241 partial result and remaining boundary

The owned references remain outside shipped crates. Initial whole helper
extractions failed retained structured-Drop/translation guards; accepted
factorings avoid those shapes without editing the pinned extractor.
`HelperComplete224.complete_result` proves the emitted arithmetic suffix equals
an ordered1024-element Result traversal, including error/failure/divergence.
`PrefixComplete224.complete_result` proves the emitted136-link prefix equals
ordered stateful actions, preserving producer-before-consumer calls and rejection.
`HelperSide224.producer_zero` exposes restored value/weight arrays and final
outer write. `HelperLength224` proves successful ordered traversals retain length.
`HelperRegistryGuard224.bounded` derives row bounds from the accepted forest
schedule, conditional on an explicit endpoint agreement check.

Prefix and suffix emissions use distinct generated field/row types. Their
conversion and relation to the original whole native helper are NOT proved.
A proposed uncompiled direct composition was removed before any compile because
it ignored that type boundary. No local component theorem is promoted to V241
closure. `HelperView224` specializes variant type op19 to the withdrawal Bool,
preserves missing vector entries as None and proves other type frames; this is
not an installed op224 callback.

[fidelity224-resume3.json](fidelity224-resume3.json) records native/emission
comparisons with changing writes: four prefix side cases and a full1024-element
suffix output with one active endpoint at1023. Both agree. These are finite
validation, not universal native equality. Feature graphs and native receipt
pins are retained; no deployed-feature credit is inferred for an unbound root.

## Final verification

Every Lean run: env J,-M7000,900s, one own6G-high/8G-max/swap0/Tasks64 scope.
All accepted axioms are subsets of propext,Classical.choice,Quot.sound.

|ID/target|Exit|Wall(s)|Peak RSS(KiB)|Scope peak(bytes)|Swap|
|---|---:|---:|---:|---:|---:|
|51997 / PV_B3P_Resume3Axioms|0|1.223|2641540|294903808|0|
|51998 / PV_B3P_Resume3CombinedAudit|0|6.598|2663056|320311296|0|
|51999 / PV_B3P_Resume3FocusedClosure|0|1.015|2645340|292605952|0|

All three use the final proof revision above. The combined audit installs132
in any original carrier and preserves all261 others, including133/226; those
inherited packets are reused, not recompiled. The focused closure is the new
V228 packet plus V241 component laws, not the privacy endpoint or a full
rebuild of the inherited V229/V243 closure.

[Receipt index](receipt-index-resume3.json) records all100 targets, statuses,
resource measurements, exact source/blob/dependency fingerprints and axioms.
[Closure hash audit](closure-hash-audit-resume3.json) checks60 current project
modules with zero dependency mismatches. All5673 external objects were SHA-checked
before the first compile (`receipts-resume3/external-verification.json`).
No revision-label corrections were needed. Original receipts and failed drafts
are retained. [ROWS7 snapshot](ROWS7-selected.json) records the selected ledger
statements without changing their scope; its research revision/hash is retained.

## Premises and cleanup

Before D377: V229/V243 closed; four selected requirements open. After D377:
V228 additionally closed; three remain open. No hypothesis was weakened, added
or moved into T. No full endpoint premise was removed: V165/V167,E1/E2,real
RunJoin,the client proof-account route and L1/L2/L3 remain substantive.
T remains exactly entropy_law,entropy_kernel,observation. Simulator and observer
are unchanged. No crates/,programs/,shared sources,other-job workspaces or keys
were changed; no push.

After all own scopes ended, own target/,charon-target/,lean-objects/ caches were
removed:328416064 bytes. Sources, receipts and hashes remain; see
[cleanup](resume3-cleanup.json) and [artifact manifest](resume3-object-manifest.json).
Resume V241 with a fresh budget/IDs, then V245,V244; do not rerun unchanged
successful proofs solely because their disposable compiled caches were removed.
