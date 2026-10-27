# L166 physical local association: obstruction at the attempt60 gate

Initial assessment after compiler20. The final budget receipt records the
attempt60 gate; no actual physical association is claimed by the source
operational theorem `BEk_LocalAssociation.of_step_projection`.

## Exact definition required

The adopted specification remains `BEh_Scope.BothSlots admitted native source`.
For ONE reached native cut, input must retain original proof bytes/slices,
Prepared queries/roots, folded root, ordinal, allocation/borrow geometry and
initial native state. State S is a common observable projection; before is
one chronological attempted history, including duplicates.

For each admitted input/slot/state/before, the goal reduces to:

```
(∀ a, native.1 = ok (Ok a) ↔ source.1 = ok (Ok a)) ∧
(∀ a, native.1 = ok (Ok a) → native.2 = source.2) ∧
(accepted native.1 = none ↔ accepted source.1 = none) ∧
(accepted native.1 = none → native.2.2 = source.2.2)
```

Here `source` is the stateful SdkC currentCode/stageCode interpretation on
those SAME source arrays and ordinal. Native must be the instrumented shipped
body with its actual attempted-call recorder; it cannot be defined by assigning
the source interpreter's log to a value-only native function.

## What the reached extraction actually supplies

`BEk_ReachedInputs.cuts` extracts both exact source batch argument tuples from
the accepted native wrappers on the fixed Entry/heap/allocator states.
`BEk_OriginalInputs.selected` additionally obtains ARU's original partial-account
cylinder and exact replay. These facts do not supply an internal native batch
heap/recorder field. D188 `First` and `Second` return Results; its stage1/stage2
fields are extensional Result equalities. `digestSource` and RuntimeSyscall bind
successful returned digest values, not an independently observed recorder.
SDK borrow_frame/guard_liveness and runtime entry admission do not themselves
construct that internal instrumented batch observation.

`BEk_RecorderIndependence.original` is checked on the original tuple and the
DERIVED reached current batch arguments: appending one extra attempt to a
separately decorated observer leaves Result and final carrier unchanged while
violating the required Law. Original support and partial-account replay remain
fixed. This is an interface non-implication, not a shipped execution/bug/attack,
and not a claim that the real runtime issues the extra call.

## Reduction shape and the non-solution

The checked operational simulation reduces a read to the two primitive goals

```
(nativeCall parts state).1 = (sourceCall parts (project state)).1
project (nativeCall parts state).2 = (sourceCall parts (project state)).2
```

followed by induction on the EXISTING effect syntax. This is small symbolic
reduction; no large recurrence, numeral normalization, finite enumeration or
scratch-induction replay is needed. `Port4B_BatchJoin.accepted/compose` already
threads the three live scratch returns in its certified denotation and is
imported unchanged. Reproving its array induction cannot produce an absent
physical recorder argument. `BEk_LocalAssociation` therefore explicitly names
its source-operational interpretation and step premise; no physical closure
credit or new admission containing the desired Law is taken.

The missing deliverable is extraction/erasure and per-step association of an
instrumented native batch on the same reached physical geometry, including
all rejected attempted prefixes. Rejected error kinds remain irrelevant:
D188 Parse-versus-panic stays a fidelity note. No rejected state equality,
new trust field or source adoption is requested or silently introduced.

## ARU is consumed; it is not the local obstruction

`BEk_OriginalJoin.accepted` composes ARU_OriginalFactory.original, OriginalLaw,
Join and Charges on the original partial account and queried cylinder. The
query-only local prefix/slot consumers now accept SdkC/ARU Returning logs
without global P1 at H. There is no waiting for ARR/ARQ_Join.Target.

ARU's universal range and unchanged independent Runtime obstruction remain
separate, as its own handoff states. This job neither assumes universal support
nor changes the actual Rc10 quantifiers. No BEk_Top.deployed wrapper is exported
as removal. L166 remains deployment-only and open. Ledger delta0.
