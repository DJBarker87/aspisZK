# NKB native cut inventory

Target not yet established. No parent row is claimed CLOSED.

## Native windows and limits

| Pair | Window | Established scope | Status |
| --- | --- | --- | --- |
| K001/K002 | Exact node-count rejection terminal | Arity Two, d<=16, unconstrained None child reply, Rust Err(Merkle), every idx/val cell unchanged | Diagnostic control only; not a real node_count law |
| K005/K006 | Exact key/opening/leaf prefix | batch0 n10 or batch1 n12, canonical high key and in-batch low byte, exact opening address/length, tree, one reply, next position | Paired argument/control support; no independent payload-byte claim |
| K013/K014 | Exact immediate dedup/write block | Arbitrary full arrays, d<16, all duplicate/append/error arms, exact count and arbitrary index/digest-byte frame | Active identical-source pair |
| K015/K016 | Exact eight-byte zero predicate | Every eight-byte word, full Boolean value | Active identical-source pair |
| K017/K018 | Actual std ChunksExact::next | One iteration, remaining length 0..5504, exact head window, count/remainder frames | Active library-fidelity pair |
| K019/K020 | Exact entered Parse-exit block | Returned Err(Parse), complete array frames; branch entry is a prior-stage obligation | Active identical-source pair |
| K021/K022 | Actual std any + exact predicate | Zero/one full chunk, arbitrary short remainder, result/call-count/iterator frames | Active kit-method-3 differential |

K003/K004 is excluded: its control timed out. K007/K008 are supplemental because source additions intervened; K013/K014 replace them. K009 timed out on the full-slot shape; K010 was cancelled. K011 timed out on the strengthened full-proof arbitrary-byte prefix; K012 was cancelled. No unchanged timed-out shape, renamed verdict workaround, cap increase or timeout increase occurred. No unproved prefix payload window is claimed as passed.

## Typed transcriptions and Lean direction

NKB_DedupCut.Cut is the K013/K014 poststate transcription. Its three constructors retain the complete arrays, cursor frame and exact append/duplicate/error split. NKB_DedupCut.source applies the existing cohort leaf-step law forward; NKB_LeafChain.source threads those exact cuts by finite induction. No inverse raw-log association or global Run/endpoint premise is introduced. The Option-none here represents the immediate duplicate error, whose parent maps to the explicit Rust Err(Merkle); it is not the faulty terminal pending-none boundary.

NKB_ParseCut.Cut is the K019/K020 local return/frame transcription. NKB_ParseCut.mismatch is a negative fact about the reused source wrapper, not an admitted parent bridge. Both definitions cite source snapshot SHA256s and assertion excerpts in their docstrings. The harness-to-definition association is the existing P6/D188 option-A ReviewedTranscription RECLASSIFICATION; no trust row is added/removed.

NKB_KeyStream.source composes CLOSED-candidate NJS key/sort laws at the SAME raw queries, lo/count/tree and sorted array, deriving the decoded index/opening stream and inactive-key frame. NKB_ProducerChain.caller and verifier_bytes prove the produced scratch's order/count/canonicality and instantiate NJV_CallerBounds.from_count on that SAME counted prefix. Their list/cut assumptions are local intermediate composition facts, never proposed whole-parent root hypotheses. NJS/NJV credit depends on ledger17.

The complete returning/aborting batch_tree root, with chronological leaf/node histories, root/Prepared/proof identity and every Result arm, is not proved. The wrapper parents therefore remain OPEN. No runtime totality, first-proof persistence, NoBad, arbitrary Ops or free reserve/outcome Bool is inserted.

## Canonical source chain

NKB_CanonicalRange.entered → NKB_CanonicalPair.source (2 iterations) → NKB_CanonicalScalar.entered + NKB_CanonicalTail.source → NKB_CanonicalScalarLoop.source (26 iterations) → NKB_CanonicalOpening + NKB_CanonicalSlotLoop.source (4 slots) → NKB_CanonicalRows + NKB_CanonicalRowsLoop.source (22 openings) → NKB_CanonicalPrefix.source. The source proof preserves every Parse branch and proves the pending-none panic arm unreachable for its total child interpretations. NKB_CanonicalDomains proves each SAME-window length without any success/canonicality premise; NKB_CanonicalGeometry proves exact coverage of all 152 words in the first608 bytes and salt exclusion. The generic root still contains the explicit scalar/K/echeck/check_values interpretations, so it is not a positive driver root under (aq)/(au); their concrete substitution and complete adopted-model equality remain OPEN.
