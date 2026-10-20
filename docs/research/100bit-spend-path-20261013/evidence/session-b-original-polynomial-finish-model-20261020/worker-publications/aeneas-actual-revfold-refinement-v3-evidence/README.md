# Aeneas actual reverse-iterator fold refinement (V3)

This focused Lean result imports only the pinned `Aeneas` owner. It proves that
for the actual Aeneas `Rev<Range<usize>>::next` operations, repeated iteration
on `[0,7)` yields indices `[6,5,4,3,2,1,0]`; a generic Result-aware loop that
uses those same actual operations is equal to a List fold over that trace. The
callback is arbitrary and may fail or diverge; the theorem preserves the
Result bind behavior.

The source-level boundary remains explicit: this is a Lean transcription of
the `rfold` loop, not a proof that Rust's standard-library `Rev::fold` source
is translated to exactly this Aeneas transcription. That Rust library
correspondence is still open. This packet does not import generated protocol
`Funs`, `FunsExternal`, or `TypesExternal` owners.

Direct imported object: `Aeneas.olean`, SHA-256
`d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d`, selected
from `/tmp/root-finish-view-host-cache-20261019/objects/Aeneas.olean`.
The selected child object `Aeneas/Std/Core/Iter.olean` has SHA-256
`c58d0fccebfd9e74d1350687592dab33580ef0af30ad293b159216c01e8e9326`.
The source pin `pins/Aeneas-Std-Core-Iter.lean` has SHA-256
`37e6d1901461e1df84f87a753ca3452eec4885e0779a12046630f5e26ea86985`.
In that source, `Rev.next` at lines 725ff delegates to `DoubleEndedIterator.next_back`; `Range.next_back` compares endpoints and uses `Step.backward_checked`.

The proof used kernel `decide` for the closed eight-call trace. It does not use
`native_decide`. All three printed theorem axiom lists are
`[propext, Classical.choice, Quot.sound]`.
