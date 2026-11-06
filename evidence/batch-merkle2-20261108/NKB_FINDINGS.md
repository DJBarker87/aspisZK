# NKB findings

Target not yet established. No parent row is claimed CLOSED.

## NKB-F1: returning errors and the reused pending-none boundary

Frozen candidate.rs batch_tree returns Err(Parse) when its count/padding guard rejects, and Err(Merkle) when node_count or verify_in_place rejects. The raw NJS emission and the adopted Port3_NativeBatchBody terminal instead use done(idx,val,none) at those tail exits; their enclosing batch_tree maps pending none to fail panic. The immediate duplicate-digest rejection is different: its explicit some(Err Merkle) is preserved and is covered by NKB_DedupCut.

NKB_Rejection.count_none checks the reused emitted rejected-count terminal. Its empty count is a LOCAL diagnostic, not a claim of reachability after a positive complete batch. NKB_Rejection.lost_error proves the pending-none boundary is unequal to any normally returned Rust Err on the same arrays. K019/K020 separately certify the exact entered native Parse-exit basic block and all index/digest frames; NKB_ParseCut.mismatch ties that local cut to the unequal boundary. Neither the native error block nor this theorem assumes whole-parent success.

Nonzero padding is an allowed rejection of arbitrary stored proof bytes. NKB_PaddingPredicate.first_nonzero is a normally returning true callback; NKB_PaddingFrame.nonzero_rejects covers the aligned suffix symbolically. The complete native parent-to-terminal reachability/trace bridge is NOT established here. K009's whole-slot attempt timed out and gives no credit. This is a source/model Result-carrier finding, not a shipped Rust bug, a demonstrated security attack, or a completed parent counterexample. A full Result-preserving root using this emission needs a corrected boundary/approved interpretation; an accepted-only or successful-child premise is not an allowed substitute. No existing module or adopted model was changed.

## NKB-F2: TX2 can retain twelve indices

The frozen batch=1 range is queries[10..22], n=12. At tree=0 or tree=1 the tree index is the query itself. Twelve distinct canonical queries therefore need not deduplicate. NKB_StrictCount proves the ascending-index build count generically. NKB_StrictLeaves.total constructs the append-cut chain for every digest stream without assuming successful insertion. NKB_DomainFinding.unit_counterexample instantiates twelve canonical indices 10..21 and proves that the SAME produced idx/val/n passed through NJV_EntryABI.initial cannot satisfy NJV_UnitDomain.Domain's <=10 field. Its only initial-counter fact is zero. The entire arbitrary initial scratch suffix is retained.

This does NOT refute NJV_TX2.TX2_093: its stronger entry refinement covers this case under the <=9216-byte gate. NKB_ProducerChain.verifier_bytes derives that gate from the SAME well-formed produced scratch and counted prefix, for <=12, without claiming twelve implies ten. What cannot be claimed is discharge of the separately retained literal ten-leaf unit clause on all TX2 calls. Preserve that original clause and reconcile/retarget it explicitly at the next ledger review; do not silently narrow the caller or weaken the unit.

Both findings are local implementation/domain facts. The headline, frozen3, security target, privacy, two-transaction game, L154 and D188 classifications, and trust inventory are unchanged. Target not yet established.
