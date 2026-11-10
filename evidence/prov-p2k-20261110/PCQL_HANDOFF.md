# PCQL_ HANDOFF: phase P2k

Target not yet established. Frozen 4bb3b3f. Branch codex/pc-prov-p2k-20261110. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p2k-20261110/. 17 of 30 Lean scopes used, 0 extraction scopes. Receipts: PCQL_L0nn/receipt.json, PCQL_SCOPE_SUMMARY.json, PCQL_ATTEMPTS.jsonl. Status: PCQL_STATUS.json, PCQL_REMAINING.json, PCQL_CLASSIFICATIONS.json.

Differences first. (1) The gate items for most externals are not definitions: in NJS_Extract.Funs, NNG_verify_finish.Funs, NMT_first.Funs, NMT_stage1_owned.Funs and AdapterRwModel they are `variable` premises or fields of the Ops structure, so "fresh = gate" is not statable; the attainable statement is a premise-discharge witness (value and type match). This is a structural fact about the gate, not a configuration difference. (2) NGD_SlotRef (nfu_reference crate): OFF_NODES is a literal Usize in the gate and Result Usize in the fresh emission, and the gate loop body uses wrapping_mul/wrapping_add where the fresh body is overflow-checked: configuration/encoding difference (checked vs wrapping), no value difference found. (3) NCX_Reference (ncx_reference crate): Result-lifted constants again, and the fresh bodies need Slice.Insts.CoreCmpPartialEqArray.ne, absent from the pinned Aeneas Std (HM-D). (4) Q.raw / Dot.finish source-shape difference carried over from PCQK: not an encoding difference, unchanged.

Closed in this job (exit 0, standard axioms only, no sorry):
- PRVEq objects compile against the L187 closure (L001), no name clash.
- field.qm31_m31_dot: fresh E010 = gate RPu_FIq_Native02 (L012, PRVEq_RPu_FIq_Native02_q1.lean).
- state_only_selected_mask_value and its cone: fresh E010 = gate AspisR1SelectedMaskProbe.Funs (L013, 46 theorems).
- r1_wire.Prefix.payload (and record): fresh E015 = gate AspisR1PrefixAggregateParser.Funs (L014).
- C1_TAG = ok 113, C2_TAG = ok 241 as the values for premises NJS_call_6/7; slot_offset typechecks as NJS_call_9 (L010, PRVEq_NJS_Extract_ext_q1.lean).
- m1b files compile (L001-L005, L007, and NFS_AccumPart00 after an alias fix as m1c, L017): 10 of the 15 EMITTED_NOT_COMPILED definitions proved. Three m1b files compile with zero theorems and are not credited.

Not closed: 17 externals (Ops/NMT premises, circle_validated), the two NCX decode_* equalities, slot_offset equality, five of the 15 definitions. See PCQL_REMAINING.json.

Gate sources for all comparisons are the L187 closure sources; the credited equalities are against the aspis_r1_mask_extraction_probe / aspis-core-field gate extractions, not against frozen-source modules.
