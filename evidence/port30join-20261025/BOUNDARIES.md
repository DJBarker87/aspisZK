# Retained boundaries (full definitions pinned, no discharge claimed)

Complete exact definitions are in source-pins.json and the referenced .lean.txt
snapshots. The following is an index, not a substitute record/axiom or claim
that its hypotheses hold for native production executions.

- Library W (Nat→Record): arbitrary `related` interpretation; accountData,
  accountLamports, cellPayload, cellCounter, liveGuard, allocated and run. No Rust
  memory instance is constructed. `Heap` includes accounts/ownerLive/allocated/
  payload/counter/external/guards/ambient. `Valid` includes token/owner pairwise
  uniqueness, signed-counter bounds and accounting, exclusive/external exclusion,
  live allocation/descriptor agreement and data/lamport cell separation.
- S2TrustedSdkBorrow retains ALL15 fields, universally over valid related states:
  account_data_cell, cell_payload, cell_counter, shared_ok, shared_err,
  exclusive_ok, exclusive_err, shared_deref, exclusive_deref (including in-bounds
  writes), guard_move, shared_drop, exclusive_drop, error_move_drop, borrow_frame,
  guard_liveness. Complete enabled-operation and reply specifications are captured
  in S2TrustedSdkBorrow.lean.txt; no field assumes caller output/acceptance.
- TrustedStd retains exactly `slice_copy_from_slice`, universally equal to its
  length-checked specification: matching lengths copy destination contents,
  retain descriptor/inaccessible contents; unequal lengths panic. Native Rust
  reference admission is still SDK/runtime. No allocator or oracle effect licensed.
- Allocator retains private allocate/cleanup Result operations. Failure/divergence
  excludes accepted branch; it has no account capability. e/e2 retain complete
  handles, records (Owned,lamports,rentEpoch), buffers/base/provenance; snapshots
  and metadata are computed. State2/world2/Entry2 remain arbitrary independent
  initial states with their own admission, not an asserted native checkpoint
  retention link. Protected-version history below supplies that conditional link.
- Runtime admission for3/7 accounts retains `related` plus Valid, empty guards,
  no external borrows, live owner handles, zero data counters and BOTH
  sharedCellsOnlyEqualKeys/duplicateKeysShareCell implications. No allocator/CU,
  inter-transaction retention, extraction or oracle premise is discharged by it.
- D188 AeneasExtraction retains ALL3 universally quantified source-function
  equalities: native stage1, native stage2, and op43=digest hashv including fail/div.
  sourceBoundary derives old digest equality through digest_eq_hashv. This is the
  standing extraction/source interpretation boundary, not native compilation or
  ELF binding. originalFirst/first_eq_original have their actual chosen dependency
  context, not whole original/current computational-body identity.
- P1.realization is ∀bytes,sha256 bytes=H bytes. RuntimeSyscall.returningValue says
  returned hashv digest decodes to sha256(flatten parts), with NO totality promise.
  The result is success-conditioned oracle correspondence, not adaptive native
  distribution, event-law, extraction-security or ROM-instantiation proof.
- ChildConeJoin.execute is polymorphic in actual typed Call A; erasure of its
  returned first component equals invoke ops call, including failure/divergence.
  FirstMarks/SecondMarks separately require local successful marked-event child
  trace projection to the corresponding FirstSegments/SecondSegments trace.
  Neither source instance nor native event correspondence is produced here.
- Conditional writer has header and size for its actual successful first_decoded
  semantic/pub/proof/split call; reader checkedHeader uses actual successful
  op11 and same HeaderDecode. Protected S2X.CheckpointVersionBinding refers to
  actual post1 committed payload and the SAME s.checkpoint. P2Prime.binding is
  fixed-pair R9PoolRuntimeBinding.P2Prime for the two concrete proof/public byte
  pairs. FirstEntryVerifier.parsed is actual compact-parser provenance;
  Multiproof.batch0Ranges/batch1Ranges are concrete checked physical slices;
  S8Stage.scanArgument is length>=7495 and the checked7031..7495 slice. Full
  hidden range definitions are captured in S2Y_OwnedChildren. No FullForest input.
- AdapterRw.Ops and AspisR1CurrentCaller.Ops are still partial typed operations,
  not certified native instances. Complete records are captured (AdapterRwModel
  and CurrentCompactCallerModelV1). Only the existing explicit current installation
  chooses codec/first/values/round/original preparation/borrowed claim methods.
  FinishModel.Boundaries retains all8 fields: fromFn,mask,add,mul,terminal,circle,
  unwrapRoot,claims, with their full Result and higher-order types unchanged.
- p/root/length parameterize exact serialized rank/query trace interpretation.
  They do not assert fresh randomness, transcript distribution, retries or abort
  laws. Native Claims/prepared_claim allocation/initializedness/drop/full-loop
  association, concrete Terminal and remaining mask/terminal domains, native
  arithmetic/Std/effects/abort correspondence remain open.

No added trust/premise. No retained boundary is relabelled as discharged. Native
refinement, final coherent kernel replay and ELF/release binding remain separate.
Current ELF pins (unchanged, no new identity validation): default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Both deployed security targets remain NOT ESTABLISHED.
