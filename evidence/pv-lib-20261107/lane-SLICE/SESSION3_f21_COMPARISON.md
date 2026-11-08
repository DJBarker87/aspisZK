# slice:f21 comparison — D983, statement candidate only

Source policy: SPEC lane a84dc05c68e, PSPEC_COMMON revision2 plus SPEC_CORRECTIONS
SPEC-C2 read-only. SPEC-C2 explicitly leaves the slice machine unchanged.
Provider source pin: STX 3eb0cb97b63aaf110327a99529cbbca93c670dca.
Candidate: lean/PV_LIB_SLICE_Spec_f21.lean, focused49921.
No row proof or full frozen-contract completion is claimed.

## Checked new package defect (not a frozen prose correction)

PV_STX2_ToVecCallSummary.Success.vector requires
`∃ inner, value = PV_STX2_SliceToVecConstruct.vector inner`.
That constructor encodes length ZERO. The actual successful set_len result is
`PV_STX2_SliceToVecFinish.vector inner (.number n)` (SliceToVecFinish.vector).
The compiled package_success_forces_zero proves that package Success on this
final source value implies n=0, independent of all machine/reply choices.
This is a contradiction of that value SHAPE for a positive final value, not a
contradiction of the full source7 composed premises, nor a source7 run witness.
The frozen PSPEC already requires final length n, so it is NOT weakened or edited.
No assertion that a theorem proves positive package Post was made or withdrawn.

Candidate Success uses the provider's final value constructor, SAME selected
fresh header, actual pointer wrapper, cap, Global allocator and length n. It
also states pointer4/dangling for n=0, the actual VecOwnership, and entry-byte
copy. It no longer imports the incorrect construction-length Success.vector.

## Literal comparison

* Entry extends the provider's Entry with arbitrary suspended configurations.
  Pre is exactly package Pre AND Numbered on each suspended configuration:
  pre_comparison. All old reference validity, source-region/header identity,
  allocator representation, old OWNER invariants, usize and live lower caller
  numbering are retained. No successful child, future read or decode premise.
* MachineSpec extends the literal package MachineSpec (machine_implies_package)
  with a full-answer malloc binding to Environment.allocation at actual
  source f59/s1683, occurrence0 within this single f21 invocation, actual id,
  [bytes,4] and pre-world. Reservation is a separate channel; none is polled
  by this f21 closure. No success answer is selected. Environment binds the
  counted primitive BEFORE checked's null-abort conversion and its event.
* Pending adds completed=none and structured resolver=none. pending_implies_old
  is compiled; no_false_pending11 rejects the ACTUAL f31 BODY push accepted by
  the old package predicate. No fallback answer is consumed for a BODY push.
* Reference chooses least corrected own boundary or all finite observable
  prefixes of an infinite trace. Candidate output is independent of reference.
  Package Post has only existential finite fuel. No first-boundary proof for
  the candidate Contract is asserted.
* Observe erases state/world/suspended frames on process abort. Elsewhere it
  abstracts the activation counter in the current store and suspended stores;
  actual runs retain numbering. Events are prior++suffix. Suspended frames
  are retained exactly up to this abstraction. Package abort framed internal
  state. No cross-callee whole-store/counter equality is introduced.
* Frame retains literal package source-cell/registry/header/WF/numbering clauses
  only outside abort. SourceFrame additionally preserves the entry source bytes
  on EVERY non-abort boundary, including fail/div/fault/pending, not only success.
  Ordered full replies/Err payloads and their effects are fixed by reference.
* Contract is a Prop definition, not a theorem, axiom, sorry or claimed instance.

## Full-contract gate is STILL OPEN

This candidate must NOT count as the requested full frozen contract yet:

1. MachineSpec still inherits the provider's arbitrary residual base carrier
   and control. Their complete actual emitted-operation inventory and named
   source/runtime meanings are not bound by adding one malloc-channel equation.
2. Reference still uses the expanded source interpreter. An exact D877 graph
   summary of f31/f32/f33 at their SAME issued operands/state, with actual-domain
   discharge and named source semantics for every allocating child, is required.
   The previous graph modules have explicit transport/firstness qualifications;
   importing them would not discharge this interface.
3. Complete heap frame outside the source-defined fresh-allocation footprint,
   lower-continuation preservation on each delivery branch, and an explicit
   all-branch allocator/runtime adequacy binding are not established by the
   current header/byte projections. These belong in the full statement, with
   no desired-post or write-definedness hypotheses inserted in MachineSpec.

Per D983's whole-contract-first order, f13 and later rows have NOT been started.
Full source7 joint witness/contradiction follows completed contracts, not this
value-shape diagnostic. No graph/entry component is credited as that witness.
