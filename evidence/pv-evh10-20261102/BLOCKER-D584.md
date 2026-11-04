# D584 — OWNER scope correction; requested conditional producer not built

Resume `062167fb6868fb08d5dcea8ac442380d2e200fd6`, same worktree and
`codex/pv-evh-20261029`. The latest instruction permits a conditional proof
before evhB4 lands. Its absence is **not** a reason to wait. No waiting,
parallel-branch import, merge, host launch or compile occurred in this resume.

## Exact OWNER meaning, without adding consequences

Read the other branch with `git show`; its revision and verbatim shared
specification are retained in `inputs-D584/`. The evhB4 prompt is retained too.
The required single Prop concerns source-bound Vec/RawVec headers and the
V183 allocator world: the same pointer owns a live allocation with the
capacity-derived extent and element alignment, or the specified zero-capacity
dangling case. This ownership must be preserved through the reached reserve,
growth, allocation/reallocation, shrink if reached, moves and drop operations,
including allocation failure and overflow. Post-world and failure histories
must be retained as specified by SHARED-VEC-D580.

This resume has **not implemented that Prop in Lean**. An unconstrained
`OWNER : Prop`, a record containing the desired execution, or an arbitrary
new header lookup would not have the requested exact meaning. Nor would
renaming the existing heap ownership relation establish the source association.
The existing V183 `World` in `PV_FXM_ReserveWorld.lean` has `live : Nat → Bool`
and request history, rather than a source-header ownership lookup. Constructing
the source-bound lookup is the evhB4 deliverable; the conditional consumer still
needs a concrete interface for its type, not a hypothesis that its conclusions
already hold.

## Correction to the D583 dependency claim

FRAME-ENTRY-D583 attributed interpretation of live stack slots, lifetimes and
active machine frames to OWNER. That is broader than the Vec/RawVec relation
in the evhB4 prompt. Those facts cannot be silently added to OWNER. D583's
statement that the frame interface was reduced to *exactly* that shared
dependency was a structural proposal, not an established reduction. This
resume withdraws that reduction claim; it does not reintroduce the retired
pre-answer stack-VMA demand. Stack grant/exhaustion remains a world answer.

The same actual-prefix interpretation must supply, by construction and proof:

* the reached entry arguments and callback capture at the required dictionary;
* source state, physical memory, stack grant/fault and active frame identity;
* association of each raw reply with that same memory and ordered world;
* native effects, outcomes, and the next call's post-world.

These are implementation/proof obligations, **not proposed new hypotheses**.
Their absence is not a counterexample to the shipped program, nor a proof
that an OWNER-only theorem is mathematically impossible once they are built.

## Exact remaining deliverable on the unchanged domain

For the original four binders in FRAME-ENTRY-D583:

```text
base : ProverRwFull.ExternalTypes
heap : R1Z.PV_RunJoin_WeightInstalled46.Heap
box  : R1Z.PV_RunJoin_WeightInstalled46.Box
ops  : @ProverRwFull.ExternalFuns
  (R1Z.PV_RunJoin_NativeResidual62.types
    (PV_EVH_NativeRawSelection.rawBase base))
OWNER : the single exact source-bound allocator-ownership Prop above
```

Construct the actual invocation/prefix carrier and ONE advancing execution
at `opsNative (PV_EVH_NativeRawSelection.rawBase base) heap box ops`.
Every effect feeds its post-world to the next effect. The carrier must include
stack and allocator answers and all failed, faulty and divergent finite
prefixes. Then prove `actual_frame_entry` on every reached entropy-entry
prefix, with the granted/exhausted alternatives in FRAME-ENTRY-D583 and the
corrected caller offsets 304/352. No extra premise for a successful prefix,
frame separation, kernel delivery or finished helper result may be assumed.

For the SAME actual runtime index `i = (env, observer, instance, randomness)`,
construct `run(i)`, its ordered events `E(i)` and faithful native terminal,
and install the following equations simultaneously in the deployed binding:

```text
rt.native env observer instance randomness = <E(i), terminal(i)>
rt.fileTrace i = PV_RJ4IDB.nativeFiles E(i)
rt.countTrace i = (PV_RJ4IDB.nativeCounts E(i),
                  PV_RJ4IDB.nativeRejections E(i))
rt.timeTrace i = PV_RJ4IDB.nativeTimes E(i)
rt.oraclePrefix i = PV_RJ4IDB.nativeOracle E(i)
```

This is still an interface specification, **not a Lean declaration or proof**.
`ActualEntropyEntryPrefix`, `stackAnswer` and `OWNER_actual_prefix` in D583
are semantic placeholders; no tracked Lean declaration for them was found.
Defining them as the desired conclusions would hide the goal in the hypothesis.

## Concrete source frontier

`NativeOperatorProver.entry_OPEN` supplies a World monad entry with many open
callees. Its `entry_fixed` theorem requires separate compatibility hypotheses;
those have not been derived from OWNER. `NativeEntropyIteration.run` still
receives an arbitrary success continuation. The later Delivered/Rejected laws
relate source branches and memory under explicit per-call kernel/frame inputs;
they do not install every primitive observation or the next advancing call.

`World.World` has no stack/resource mapping answer. `StackCleanup.Run` has a
native outcome and physical state, but is not the full entry producer.
`Runtime.Outcome` retains fault/exhaustion separately; `NativeTrace.Terminal`
has success/failure/panic/abort/diverge. A conversion must obtain the actual
panic/abort information, not map faults to entropy errors or fuel exhaustion.

All five `rtDeployed` selectors still read their corresponding OPEN inputs.
OWNER places no constraint on independently supplied trace fields. Changing
selectors to project an arbitrary supplied NativeTrace would only relocate
that open input. This audit does not make such an installation.

## Validation and status

`check_owner_scope_d584.py --check` pins the shared specification, evhB4
prompt and inspected tracked sources, and checks the concrete open selector,
continuation and carrier facts above. This is a source inspection certificate;
it is not a Lean theorem, a counterexample against an actual deployed run,
or proof of impossibility. No new Lean Prop/theorem, axioms audit, native
execution, full regression, release replay or resource scope is claimed.

The requested conditional construction is incomplete. No endpoint/deployment
row removed, no new assumption or trust field, T unchanged. D520/U/D524,
V370/V371/V400, NativeObstruction62/op132, L1/L2/L3 and actual non-emptiness
remain. Next Lean90259, then91500–91599 with reserved audits; nativeN91603.
No key/account/funds action. Stop is on the unimplemented actual source/world
interpretation and complete producer under the inherited focus rule, not on
waiting for evhB4 or exhausting resources.
