# Phase-owner diagnosis and retarget

Stage 1, source revision `fd75008be31e1f4bc2a5cecc122171098b14ee4e`.

The conflicting name is `AspisR1PublicPreparation.verifier.Phase`.
`S1SemanticPhaseV1` declares it as an abbrev of `AspisR1PublicPreparation.FirstCaller.Phase` (immutable source in NFN_SOURCE_GRAPH.json). The headline's `AspisR1PublicPreparation.Types` owns it as an independent inductive type. NFN_L002 prints both actual declarations. They are NOT definitionally equal: the first unfolds to the FirstCaller inductive; the second is the verifier inductive. Both have Parsed, Semantic, SemanticPart(U8), Prepare, CheckpointRead, Merkle(Usize), Query(Usize), QueryPart(Usize,U8), CheckpointWrite, Relation, Final, with the same payload types. An explicit constructor-preserving bijection will be proved; neither owner will be edited or redeclared.

No NFB theorem statement directly mentions Phase, including its aliases: NFN_PHASE_STATEMENTS.json records every NFB source and all Phase occurrences (all empty). The import dependency, not a geometry observer premise, introduces the conflict. In particular:
NFB_GeometryComposed → ... → NEW_GeometryArithmetic → ... → FIo_NativeTypes → NP6_StdModel → ClaimsUnrolledFinish → S1SemanticFinishBoundsV1 → S1SemanticFinishModelV1 → S1SemanticPrefixModelV1 → S1SemanticPhaseV1.

The only NP6 declaration used by the emitted FIo type file is `ReserveError`, definitionally the error owned by `AspisR1ClaimsUnrolledParent.Types`. Retargeting this unused phase-bearing std import to the error's actual owner preserves the field type. The new forest will import canonical Types, retain all Result/domain/state/effect statements and reuse copied proofs with explicit per-module provenance. No geometry observer is fabricated and no Phase is redefined.

NFN_L001 was a pre-elaboration input failure: the own cache copier did not traverse a directory symlink in NFG_standard_view, leaving Aeneas/Command missing. NFN_copy_library.py copies the actual selected library bytes with hashes, preserving validation. NFN_L002 succeeds after this own-input repair. Both attempts are retained; no timeout/memory-killed shape was rerun.

Only focused cached-cohort development evidence is claimed. Frozen Rust, three ELF pins, security metric, privacy and two-transaction design remain unchanged. No Kani, extraction, key or chain operation.

## Retarget implemented

NFN_PhaseTransport.legacy_roundtrip/owner_roundtrip prove the exact constructor/payload bijection, without axioms; observer_none and observer_some state its observer action explicitly. This is a carrier transport, not definitional equality of the two nominal types. Geometry uses no legacy observer, so no observer restriction is added.

Before: FIo_NativeTypes imports NP6_StdModel for its ReserveError alias, pulling the whole Claims/S1 phase forest. After: NFN_GeometryPart00 imports NFN_ReserveOwner, whose alias unfolds directly to the SAME AspisR1ClaimsUnrolledParent.alloc.collections.TryReserveError. NFN_ReserveOwner.error_owner is rfl, without axioms. Canonical AspisR1PublicPreparation.Types enters through NFN_PhaseTransport; no new Phase declaration exists.

NFN_generate.py reuses 87 upstream source modules in nine prefix-owned compilation units. Every original file boundary, original source/path/hash, target module and namespace map is in NFN_RETARGET_PROVENANCE.json; the original bytes are stored once in NFN_SOURCE_GRAPH.json. Proof namespaces are prefixed NFN_; emitted carrier/function names remain unchanged where needed to preserve existing external interfaces. These are copied existing proofs, not independent new proofs of arithmetic. All non-import bodies are checked by deterministic regeneration; only the definitionally equal ReserveError owner and the recorded namespace names change. No premise, Result branch, carrier payload, state/effect/frame conclusion or frozen function changes.

NFN_L006/L007/L008/L010/L011–L015 compile the nine units in dependency order, under the fixed caps. Every theorem created in each new unit (including generated/private lemmas) gets #print axioms via an environment enumeration. All passing receipts contain standard axioms only. NFN_L005 failed on our theorem-enumeration syntax, repaired by using toList.forM. NFN_L009 failed because the own namespace mapper also renamed the emitted type NFB_RowRef.NFB_RowLog; the generator now explicitly preserves that emitted carrier. Failed drafts, including their sorryAx diagnostics, earn no credit. These are input/name repairs, no timeout/memory rerun or change of a Kani verdict.

The complete NFB theorem statements are preserved under the recorded namespace substitution. In particular NFN_NFB_GeometryComposed.result_state_effects has exactly the original full model Result/persistent-state/semantic-effects conclusion; accepted_physical has the same root accepted Result and Deployed-domain premises and derives the same original query array, gather/terminal buffers, ordered trace, returns and frames. Native interpretation remains the inherited checked hybrid packet and explicit root runtime/physical/tool/allocator boundary. No cryptographic assumption is discharged.
