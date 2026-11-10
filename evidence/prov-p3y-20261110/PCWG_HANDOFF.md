# PCWG_ handoff (job pc-prov-p3y, phase P3y)

Target not yet established. Frozen 4bb3b3f; branch codex/pc-prov-p3y-20261110; host workspace /home/dombarker/project-offloads/codex-pc-prov-p3y-20261110/.

Set: the 33 PCXI_RECEIPTS records with verdict TEXT_DIFFERS "item text differs from every frozen item of that name" (PCWG_SET.json): NCV 11, NCX 12, NEG_PushActual 8, NGD 2.

Result: 12 SETTLED, 21 NOT SETTLED (PCWG_STATUS.json, per item with class and evidence). No value difference at a matching configuration was found (PCWG_DIFFERENCES.json lists the encoding differences).

SETTLED (all exit-0 scopes, standard axioms only, no unproved placeholders, no native_decide, no raised heartbeats; statements against compiled gate constants):
- NEG_PushActual power_limb_at, residue_limb_at, update_residue_row_loop0 and .body: fresh = gate (rfl). loop1 and loop1.body: loop-return refinement (gate drops the iterator from the done payload), via PRVEq_P3W.loop_map. File PRVEq_NEG_PushActual_Funs_p3y.lean, scope PCWG_L001. Fresh text is the P1n emission; the NEG gate Funs equals the NEI gate Funs except the namespace.
- NGD_AtG.shape: frozen item r1_wire::row_shape (not the same-name v8_privacy_affine_gate::shape), fresh = gate as functions. PRVEq_NGD_AtG_Funs_p3y.lean, PCWG_L008. NGD_SlotRef.OFF_NODES: fresh compact.OFF_NODES = ok gate. PRVEq_NGD_SlotRef_Funs_p3y.lean, PCWG_L005.
- NCX_Reference: POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK, required_binding_is_zero (function equality), validate_verifier_registry_v2 and validate_verifier_registry_entry_v2 (fresh mapped through explicit error/struct maps = gate). Fresh emission PCWG_E001 (aspis-statement, Aeneas original, overflow ON, 36 s, 0.7 GB RSS). PRVEq_NCX_Funs_p3y.lean (PCWG_L025) with generic lemmas PRVEq_NCX_Lemmas_p3y.lean (PCWG_L020: zero loop spec by induction over the Aeneas loop unfolding, array equality as list equality).

NOT SETTLED:
- NEG update_residue_row and BatchedWeights.push: DEPENDS_ON_LIBRARY_TRUST, external MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter (gate hand model back type differs from the fresh external; rows HM-B/HM-D).
- NCX decode_verifier_registry_v2 and decode_verifier_registry_entry_v2: DEPENDS_ON_LIBRARY_TRUST, external axiom Slice.Insts.CoreCmpPartialEqArray.ne (HM-D) and conversion models.
- NCX magic, word, zero, zero_loop, zero_loop.body and NCV bytes32*, digest*, identity, zero*: GATE_ONLY_HELPER (no frozen item of that role; same-name frozen items are unrelated). The zero loop semantics is proved and used, which is not a fresh = gate equality.
- NCX VerifierEntryStatusV1: type encoding differs (discriminant isize in the gate, u8 in the frozen emission); isomorphism proved, not claimed equal.
- NCV EMPTY: counterpart is aspis-pool empty_roots.rs; the pool crate was not extracted.

Ran: 25 Lean scopes (5 exit 0: L001, L005, L008, L020, L025; the rest are probes or iteration), 1 extraction (PCWG_E001, exit 0). Each Lean scope 1 to 56 s, peak RSS about 2.6 GB, swap 0. PCWG_SCOPES.json, PCWG_ATTEMPTS.jsonl. Not run: gate, manifest, Kani.
Process notes: PCWG_L014 reran an unchanged source (sed -i failed on macOS) and PCWG_L021 ran a stale generated file; neither carries a claim. PCWG_E001 pins cargo_jobs 1 although the command line has --jobs 4 (see PCWG_CLASSIFICATIONS.json); the next extraction spec must also set CARGO_BUILD_JOBS=4.
Remaining: PCWG_REMAINING.json. Next concrete deliverables: extract the frozen TX2 decoders (aspis-statement pool_v1 format.rs and the pool crate) to replace the NCV reference; a conditional statement for decode_* with the HM-D model equation as hypothesis.
Target not yet established.
