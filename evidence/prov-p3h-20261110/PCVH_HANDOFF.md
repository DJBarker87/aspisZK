# PCVH_ HANDOFF: phase P3h

Target not yet established. Frozen 4bb3b3f; nothing pushed; no ledger/trust/contract/source change. Lean scopes 22/40, extraction 0, one at a time, caps unraised.

Finding first: NO counterexample. WideExact.from_le_bytes fresh (frozen eight-limb decode + from_limbs, emission PCUJ_E005) = gate R1CandidateWideParserSource (two QM31 halves) as functions on ALL inputs (any slice, any length, non-canonical limbs included): PRVEq.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes, PRVEq_PCVH_R1CandidateWideParserSource_k1.lean, PCVH_L008, exit 0, wall 5.3 s, peak RSS 2.6 GB, swap 0, axioms propext/Classical.choice/Quot.sound. Byte order and limb grouping agree (limb i = bytes 4i..4i+3 little-endian in both; QM31 halves are limbs 0-3 and 4-7). Config ON. Proof: pure decoders dec_cm/dec_qm/dec_w, gate-side lemmas cm31_eq/qm31_eq/wide_eq, a case-split chain lemma, fresh side by rfl. This supersedes PCQI-C6 (DIFFERENT_BODY, not proved) for from_le_bytes: now EQUALITY_PROVED.

Item 2 (32 ON-pinned-uncompared): 7 more credited (PCVH_item2.json): EbyKFinish from_limbs, QueryGeometry TABLE_A/TABLE_B, CurrentCompactCaller compact.LOGICAL_Y1 and compact.SPLIT, FinishCandidateExplicitOps transport.Variant.folds, Stage2 Reader. 25 open, classified in PCVH_CLASSIFICATIONS.json (mostly pins that were name-suffix matches with no declaration in the emission).
Item 3: not attempted (Array-mapping Equiv not written).
Next: type-name map for QueryGeometry fibre_point/table_value; extraction for the NOT_EMITTED items; VTop_Model generator repair.
