# D585 — remaining actual-prefix instantiation, after concrete FRAME interface

FRAME now has a real Lean data interface and checked local consistency and
preservation laws. Read FRAME-D585.md and frame-D585.json. OWNER remains
separate and is neither defined nor consumed here.

The following is the exact next interface-construction target, after the
producer exports the unchanged actual paired-prefix carrier. The carrier
name below is still the inherited domain specification, not a new Lean type
invented by this resume:

```text
(base : ProverRwFull.ExternalTypes)
(heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
(box : R1Z.PV_RunJoin_WeightInstalled46.Box)
(ops : @ProverRwFull.ExternalFuns
  (R1Z.PV_RunJoin_NativeResidual62.types
    (PV_EVH_NativeRawSelection.rawBase base)))
  |- PV_EVH_FrameSource.Correspondence base heap box ops
       (ActualEntropyEntryPrefix base heap box ops)
```

Unlike D583's placeholders, Correspondence is now an elaborated Lean
structure. Its concrete fields are view/sourceState/sourceMask/sourceRetry/
sourceLimit plus state_eq/retry_eq/limit_eq/mask_backing. The view contains
actual thread/activation/sp/load bias, source/native State, stack-limit
request and pending/granted/exhausted answer, bounded structural retry
history and loop index. It must be obtained from the SAME reached finite
paired source/machine execution, not independently selected model data.
The constructor is NOT supplied here, and cannot be inferred from the local
geometry theorem. No successful-prefix filter is allowed.

Once constructed, correspondence_consistent derives table separation and
retry depth without a separate separation hypothesis. source_slots connects
prospective existing source descriptors at the same State/sp. To finish
actual_frame_entry additionally bind all existing source live slots and
physical activation identities (including spills/copy channels) to this same
history, and combine with the separately supplied allocator interface; this
resume does not claim exclusion of arbitrary old source State slots or heap
blocks. The coarse PhysicalFrame.live predicate is not an exact decoder for
older caller Result lifetimes; use all-table geometry, and derive exact
initialized extents/lifetimes from reached source/binary phases.

The full entry producer, kernel association, faithful terminal, five runtime
selectors and actual-domain non-emptiness remain unchanged. They are not
part of the current FRAME-only task. No endpoint premise was removed, no
T field added, and no OWNER-only reduction reinstated. The FRAME interface
and its local proofs are delivered; the actual-family instantiation remains
an explicit interface boundary, not a claimed deployed proof.
