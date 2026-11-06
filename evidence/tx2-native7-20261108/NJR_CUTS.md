# NJR corrected parent cuts

TX2:065 OPEN; target not yet established. Frozen Rust revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Scratch-only cfg(kani) harness patch; shipped sources unchanged. Option-A native semantic transport is P6/D188 reclassification, not trust removal. Exact native source assertions and hash are pinned in NJR_CUT_SOURCE_PIN.json and NJR_Cuts/NJR_ReaderCut docstrings. An address is never used to infer payload.

| Member / native cut | Selected PASS | Matched semantic FAIL controls | Domain |
|---|---|---|---|
| M03 / pending_destination | NJR_K039 | NJR_K040, NJR_K041 | raw64, arbitrary selected weight window and actual destination index<64 |
| M04 / query_weights | NJR_K046 | NJR_K047, NJR_K048 | complete owned weights64 plus all-field query Result |
| M04 / query_raw | NJR_K030 | NJR_K031, NJR_K052 | complete owned raw64 plus all-field query Result |
| M04 / query_scalars | NJR_K032 | NJR_K033, NJR_K034, NJR_K035, NJR_K036, NJR_K053 | full rhs8/power4/next/terms and every Error variant |
| M05 / flush_receiver_window | NJR_K037 | NJR_K038, NJR_K054, NJR_K055 | full immutable raw64 receiver/index and selected arbitrary mutable K slot |
| M05 / flush_destination_window | NJR_K049 | NJR_K050, NJR_K051 | one actual arbitrary64-vector enumerate/iter_mut step, destination and full frame |
| M09 / reader_backing | NJR_K042 | NJR_K043, NJR_K044, NJR_K045 | SAME1768 backing/window, input cursor, full Reader reply/post, owned Err/drop event and successful64-vector frame |

M03 logs the actual `Vec.index_mut` reference used by the assignment and proves base+index destination, full metadata and every observed raw word. It uses one raw64 vector and one selected weight window, rather than the timed-out two-vector shape.

M04 supplements the retained SAME query call-argument cut at the actual returned Result/destructuring. Three windows cover full raw and weight payload/ownership/length/capacity and all rhs/power/next/terms fields, including Err. Same-valued fresh Vec controls fail; pointers alone do not supply payload. The return-boundary packet does not independently prove earlier call arguments.

M05 splits the full immutable receiver plus selected slot from the actual enumerate/iter_mut destination and arbitrary mutable-vector frame. Both SAME receiver/index and full declared receiver payload are checked. NJR_FlushComposition supplies finite composition and complete model Result/canonicality without a native whole-buffer loop.

M09 logs the SAME parent-created Reader backing and full bytes, pre/post cursor, complete reply, successful owned Vec frame, and the explicit owned-drop/error prefix. The native Vec drop executes; the drop-event control does not claim a standalone deallocator theorem. NJR_ReaderCut is a transcription of those observed fields only.

M06 uses NJF_Root.finish only through a derived SAME-call NIG_FinishInput.Domain. NJR_FinishAtSourceView gives the entire finish law at the literal source View from strict SAME-proof scan history and SAME resume/query/flush. NJR_HistoryBinding derives first-proof history from headline parser facts and transports it only with exact bytes or the existing conditional P2Prime branch. NJR_AcceptedFinishDomain derives the current proof's domain by accepted-source inversion, including collision branches, but cannot justify installing a positive native bridge on arbitrary rejected entries. No Domain, raw History, successful finish or source-endpoint premise is added to a positive root.

M07 installs the emitted generic filled at the actual raw source occurrence and the existing weight filled law with the SAME quantified Reservation. Both success and all error arms remain; no hypothesis restricts Reservation to success. Retained NJJ native allocator occurrence/ownership controls are reused with provenance.

M12 is derived at the caller: NJR_ChecksumAtHeadline.accepted_pair obtains the SAME SourceCuts from accepted native transactions, then proves proof57607/public1880 from the actual authenticated guard and encoded array. These auxiliary parameters are not a positive-root Ops dictionary. Concrete forward root invocation still must instantiate the returned witnesses.

NJR_RootAudit prints the full current NJJ_Common.run and complete relevant finish/caller statements. No positive TX2:065 root is declared. The exact remaining member and hypothesis inventory are in NJR_REMAINING.md.
