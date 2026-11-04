# Phase-owner diagnosis and retarget

Stage 1, source revision `fd75008be31e1f4bc2a5cecc122171098b14ee4e`.

The conflicting name is `AspisR1PublicPreparation.verifier.Phase`.
`S1SemanticPhaseV1` declares it as an abbrev of `AspisR1PublicPreparation.FirstCaller.Phase` (immutable source in NFN_SOURCE_GRAPH.json). The headline's `AspisR1PublicPreparation.Types` owns it as an independent inductive type. NFN_L002 prints both actual declarations. They are NOT definitionally equal: the first unfolds to the FirstCaller inductive; the second is the verifier inductive. Both have Parsed, Semantic, SemanticPart(U8), Prepare, CheckpointRead, Merkle(Usize), Query(Usize), QueryPart(Usize,U8), CheckpointWrite, Relation, Final, with the same payload types. An explicit constructor-preserving bijection will be proved; neither owner will be edited or redeclared.

No NFB theorem statement directly mentions Phase, including its aliases: NFN_PHASE_STATEMENTS.json records every NFB source and all Phase occurrences (all empty). The import dependency, not a geometry observer premise, introduces the conflict. In particular:
NFB_GeometryComposed → ... → NEW_GeometryArithmetic → ... → FIo_NativeTypes → NP6_StdModel → ClaimsUnrolledFinish → S1SemanticFinishBoundsV1 → S1SemanticFinishModelV1 → S1SemanticPrefixModelV1 → S1SemanticPhaseV1.

The only NP6 declaration used by the emitted FIo type file is `ReserveError`, definitionally the error owned by `AspisR1ClaimsUnrolledParent.Types`. Retargeting this unused phase-bearing std import to the error's actual owner preserves the field type. The new forest will import canonical Types, retain all Result/domain/state/effect statements and reuse copied proofs with explicit per-module provenance. No geometry observer is fabricated and no Phase is redefined.

NFN_L001 was a pre-elaboration input failure: the own cache copier did not traverse a directory symlink in NFG_standard_view, leaving Aeneas/Command missing. NFN_copy_library.py copies the actual selected library bytes with hashes, preserving validation. NFN_L002 succeeds after this own-input repair. Both attempts are retained; no timeout/memory-killed shape was rerun.

Only focused cached-cohort development evidence is claimed. Frozen Rust, three ELF pins, security metric, privacy and two-transaction design remain unchanged. No Kani, extraction, key or chain operation.
