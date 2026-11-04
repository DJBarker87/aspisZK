# D587 — full actual-prefix instantiation not constructed

Resume base `7356208133e924f6caabb8e2136a370ee6f02035`, same worktree and
branch `codex/pv-evh-20261029`. Read FRAME-D585.md and HANDOFF.md first.
The requested actual-family instantiation and OWNER-only theorem were not
completed. This is an implementation/proof frontier, not an impossibility
result or a counterexample to the shipped program.

## Exact missing construction

The required target remains the following specification, with unchanged
binders. It is **not an elaborated Lean declaration**: the actual-prefix
carrier in its result has not been implemented in this checkout.

```text
actual_correspondence
  (base : ProverRwFull.ExternalTypes)
  (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
  (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
  (ops : @ProverRwFull.ExternalFuns
    (R1Z.PV_RunJoin_NativeResidual62.types
      (PV_EVH_NativeRawSelection.rawBase base))) :
  PV_EVH_FrameSource.Correspondence base heap box ops
    (ActualEntropyEntryPrefix base heap box ops)
```

`ActualEntropyEntryPrefix base heap box ops` must be the full fixed family
specified in PHYSICAL-D581.md: finite prefixes of the adopted proof-account
entry paired with its source execution at exactly
`opsNative (rawBase base) heap box ops`, at relocated PC 0x1457ef after the
mask and iteration guards. All reached retries, pending resource answers,
and prefixes followed by failure, fault, exhaustion or divergence remain.
Membership cannot require frame separation or eventual success.

The constructor must derive `view` and the source selectors from that same
history and prove `state_eq`, `retry_eq`, `limit_eq`, and `mask_backing`.
In particular, its memory is the same process memory, its mask is the actual
source argument backed at sp+304, and its iteration is the reached source
retry argument with limit16. These are not choices a slot-table generator
can make independently. No constructor of this carrier or correspondence
was added in D587.

## Why the existing finite shapes do not instantiate that target

`PhysicalFrame.interpret` already uniformly handles every Fin8 retry index
and Fin16 iteration, symbolic thread/activation/sp and every stack answer.
Its table geometry and depth results therefore need no per-prefix proofs.
What remains is the connection from the actual reached history to those
parameters, not enumeration of the 128 index pairs.

`FrameSource.EntryView` accepts a State, sp, identities, load bias and stack
answer as fields. `FrameSource.rip` computes the initializer PC; it does not
establish that a machine reached it. The existing `Prefix.P` is a function
from `World` to `Prefix`; that World has counters, files and oracle history,
but no machine PC, stack pointer, mapping or process memory. The OPEN entry
and its conditional Result projection do not supply the missing paired
history. Naming EntryView, or a subtype containing the correspondence
equations, ActualEntropyEntryPrefix would replace the requested domain with
supplied model data or assume the very link being requested.

There is a further concrete FRAME obligation before actual_frame_entry:
bind **every** existing source live slot to its actual physical lifetime and
storage. The required conclusion, on the same actual q, is:

```text
forall (old : PV_EVH_StackZero.Slot), old ∈ state(q).frame.live ->
  forall i : Nat, i < old.initialized ->
    PV_EVH_EntropyDeployedLayout.OutsideFrame sp(q) (old.address+i)
```

Table separation for distinct SlotId values does not establish this
quantifier over the unrestricted source `frame.live` list. In particular,
one cannot infer initialization/liveness of older Results from the coarse
`PhysicalFrame.live` summary, as D585 explicitly records. Source/machine
identity, spills/copies, ABI alignment, and same-prefix resource replies
must come from the paired interpretation, not from allocator OWNER.
`EntropyDeployedLayout.live_frames` and `original_admission` still take this
live exclusion as an explicit hypothesis. No new such hypothesis was added.

## OWNER-only request and status

The exact shared evhB4 specification remains Vec/RawVec pointer/capacity/
length/layout ownership in the V183 allocator world, preserved through
reached operations and every failure branch. The pinned prompt and shared
specification are retained in inputs-D584/. There is no exported concrete
`OWNER_actual_prefix` declaration in this checkout. This is not a reason
to wait for another branch, and no waiting or parallel-branch import occurred.
It also does not authorize extending OWNER with stack/live-slot, PC, mask,
or reachability facts. D587 did not invent a substitute OWNER or an opaque
Prop. The requested named concrete Prop and conditional theorem remain
unimplemented, rather than being presented under a guessed interface.

The inherited D580 focus rule says to stop at a blocked actual-instance
step and state the exact missing construction. This checkpoint follows that
rule; it does not claim budget exhaustion. The next substantive work is the
paired source/machine prefix producer above and induction establishing its
source-live interpretation, followed by actual_correspondence and the full
branch-valued frame theorem. The granted branch must retain all five
conjuncts of FRAME-ENTRY-D583, while pending/exhausted branches preserve their
same-world events and continuation behavior under rdea-2'. The old D583
OWNER-only claim stays withdrawn.

Validation: check_actual_prefix_d587.py --check pins the inspected sources
at the resume revision and checks exact-name declarations across all tracked
Lean paths. This is source inspection, **not** semantic absence, reachability,
a Lean theorem, or a release audit. No new Lean/native attempt, host scope,
axioms audit, full regression, or manifest replay. D585 proofs and their
SUMMARY-BASED axiom evidence are reused unchanged. Next Lean90267 and
nativeN91603; subsequent blocks/reserved audits unchanged.

Endpoint/deployment rows removed NONE; target not yet established; T unchanged.
FRAME actual-family binding, shared OWNER, actual non-emptiness, full advancing
entry, same-prefix kernel association, five projections, V370/V400, D520/U/D524,
NativeObstruction62/op132 and L1/L2/L3 remain. No keys/accounts/funds action.
