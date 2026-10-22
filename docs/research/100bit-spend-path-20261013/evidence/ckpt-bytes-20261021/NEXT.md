# Explicit checkpoint cone consumer contract

The final source join is not currently proved. Its endpoint remains
`OraclePortCkptAbi5Stage.reached_stage`, through `strictStage`, then
`OraclePortCkptAbi5Decision.decision_observation` and dV_frozen2.
The existing reference equality retains six ordered digest reads; it does
not permit erasing checkpoint operations.

The requested final source theorem must name these independently:

1. `S2S10CallerBinding`: the retained proof/public/checkpoint carriers,
   exact source checkpoint Site/call position, source returned-state/error
   dependencies, and transaction-pair/account snapshot binding.
2. `S1S7S8StateProvenance`: reached source Prepared fields plus initial,
   saved and resumed RHS/power/all 64 weights equal the specified recurrence
   states. next=10/22 and CFG chronology alone are insufficient.

These are deliverable interfaces, not newly assumed axioms or a structure
containing an unproved complete checkpoint equality. This packet does not
create a theorem pretending that naming them discharges the missing source
codec/reader/allocation implementation instances.

Before that endpoint is instantiable, the exact next byte theorem is
`CheckpointBytesBody.body_byte_c5` (new aggregate, not yet proved): for every 0<=i<1736 on canonical S2/saved-ten source fields,
body_byte succeeds and its byte equals the reference C5 body[i]. All local source intervals, including query-byte arithmetic and weights,
are now proved by CheckpointBytesSparseE/SparseK/SparseDigest/Header/Query.
Compose them with CheckpointBytesLookup and a concrete source-to-Fields
interpretation; then transport the checksum input/output by congruence. Do not evaluate a
1736-byte term or unfold 64 field writes in the kernel.

For strict field decoder adoption, establish the exact-16 section width for
K before asserting canonical-input iff; the extracted K decoder itself
accepts trailing bytes. The E decoder has its own exact-32 guard. Complete
word_spec-to-C5 output meaning and all malformed-byte Result branches remain
necessary; successful-result canonicality is already inherited.

Production resume also needs its Reader/ResumeOps implementation instance,
including fallible reservation/resize and Box. The bounded-list content
model and prior Kani no-malloc-failure gates do not establish physical
allocation availability. A correct accepted-source refinement can derive
successful reservation from actual source success; an unconditional
encode/decode-success theorem over all allocator states cannot do so.
Preserve Allocation in an all-result theorem. Do not hide this in either
caller binding or RHS/power/weights provenance.
