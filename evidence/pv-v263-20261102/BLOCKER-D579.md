# D579 — stopped at deployed-source binding

Entry ce04bc0116, branch codex/pv-runjoin-20261026, same sparse worktree.
Target not yet established. User's D579 focus overrides the older instruction
to spend the whole budget: stop when a requested step is blocked. No new local
law, source model, endpoint premise, or implementation change was added.

## Step 1: exact missing handle-push adapter law

Frozen source is checkpoint 9c131667ca00f4daae78da6299b09a9fe0d00da9,
not the later candidate tip that no longer contains host_work.rs. All eight
committed source inputs still byte-equal that checkpoint and their recorded
SHA256 pins (binding-blocker-D579.json).

The concrete source statement is native_workers.rs:
`handles.push(scope.spawn(move || run(k)))`, k=1..15.
RetainedSpine.forks invokes RetainedMethods.push, which invokes
`runtime.methods.vector (.push 2 0 length layouts.handle)` unconditionally.
GrowingPush.push instead branches on the owned physical capacity: a reserved
push makes no resource request; a full push calls resize before committing the
new allocation and stored value. OwnedForks uses this latter operation, but the
whole RetainedSpine still uses the former. Neither is a source-bound native
adapter. This is an unresolved association, not a counterexample to Rust.

The exact required *value-erasure* equality at this boundary is below. All
operations and carriers on its two sides already exist; no new relation or
success predicate is hidden in the equation. In the namespaces used by these
modules, with `A := PV_V263_RetainedSpine.Task S B`, its statement is:

```lean
PV_V263_BufferLoop.mapAction
  (fun (o : PV_V263_OwnedDrain.Owner A) => o.initialized.values)
  (PV_V263_GrowingPush.push growth handles task) w =
PV_V263_BufferLoop.mapAction
  (fun (b : PV_V263_VectorDrain.Buffer A) => b.values)
  (PV_V263_RetainedMethods.push runtime
    {layouts with item := layouts.handle} 2 0 handles.initialized task) w
```

Required binders: S B : Type; runtime : RetainedMethods.Runtime S;
growth : RawGrowth.Runtime S; layouts : RetainedMethods.Layouts;
handles : OwnedDrain.Owner A; task : A; w : World.State S.
The obligation is to CONSTRUCT the native runtime/growth pair and establish
this equality for every handle owner/task/world reached by the deployed spawn
loop, with handles.allocation.layout = layouts.handle and its native allocation
validity invariant. It is NOT a theorem for arbitrary runtime/growth pairs:
the unrestricted abstract vector hook can fault on a reserved push, whereas
GrowingPush.reserved cannot. No such hook law may be assumed as an endpoint
premise. The native allocation invariant and native adapter construction are
also absent; the displayed equation is a precise missing lemma specification,
not a newly declared, elaborated, or proved Lean theorem.

Equality here is of World.Run, including every Result/fault/exhaustion outcome,
post-world and event prefix; the mapping erases only successful ownership
metadata, not faults or events. Buffer capacities must not be equated: they
are lower bounds and need not equal physical capacities. Even this necessary
lemma would not alone complete own-1: the native stores, all remaining source
steps/drop glue, TLS/scope/packet lifetimes and permitted scheduling still need
statement-by-statement association. No machine-code theorem is demanded here;
V370 and D381/D386 remain the existing compiler-preservation boundary.

No complete own-1 certificate or pinned direct-extraction receipt for this
whole deployed body was found among the V263 binding artifacts inspected.
No extraction was attempted and no claim of extractor rejection is made.

## Steps 2 and 3

Stopped after identifying the step-1 blocker, per the explicit instruction.
NativeResidual63.opsNative is unchanged; NativeFrames63.op257 and
V263_NativeBoundary.retained still show exact residual op257 forwarding.
Installing an unbound port would not meet step 2. The partial source projection
on native faults is retained; faults must not be fabricated as fail/div.
Actual reached capture success/Nonempty P remains unproved. A granting trace
is permitted by rdea-2, but does not supply the missing source association or
actual encoder/SemanticOracle callback laws. Public failure timing remains the
named V400-257 request-count/size/answer-timing obligation.

## Validation and before/after

Read-only source-pin comparison and inspection only: eight pinned source files
match; seven current proof/model hashes recorded. No Lean/native/Kani launch,
axioms audit, full replay, SBF/ELF build, or key/funds operation. Old compile
receipts are reused only as historical evidence, with no new validation claim.
V263 OPEN -> OPEN; op257 residual -> residual; Nonempty P unproved -> unproved.
No premises removed, added or changed. Three TrustItems, seven links, observer,
simulator and release pins unchanged; V183 remains SUSPENDED(K-3).
Skeleton consistency: reduced to non-emptiness.

119 normal Lean and 14 native remain; next 79975 (then 91300..91396), N90126.
Audit IDs 79997..79999 and 91397..91399 unused. The existing wrapper still needs
its authorized ID/budget-only extension before the first 913xx launch. No host
or launcher changes made. Next deliverable: the source-bound native adapter
and the displayed handle-push equality, followed by whole-spine association;
then actual installation and reached granting execution.
