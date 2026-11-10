# PCVL_ HANDOFF: phase P3l (top verifier equalities)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; nothing pushed or merged; no trust row added. Frozen 4bb3b3f. Branch codex/pc-prov-p3l-20261110. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p3l-20261110/. Lean 7/40 (PCVL_L001-L007), extraction 4/4 (E001-E004), one scope at a time, caps unraised, swap 0, longest Lean wall 50 s (a failed probe), peak RSS 3.06 GiB.

## Difference at a matching configuration
None found. All differences met are naming/carrier or encoding (PCVL_CLASSIFICATIONS.json).

## Claims (exit-0 scope; axioms propext, Classical.choice, Quot.sound only; no sorry/axiom/native_decide; no raised heartbeats)
1. VTop_Stages tx2_common and tx2_authenticated (PRVEq_VTop_l1.lean, PCVL_L004): for every Ext (the 23 externals of the PCVJ_E002 emission, as fields, not axioms) and every gate ops with Bound ops x, fresh = gate ops, at all arguments. Bound binds the gate's op18 to the fresh expanded resume, the gate's constant fields to the fresh compact constants, and the other used fields to Ext fields. bound_exists shows Bound is satisfiable. CONDITIONAL_ON_BINDING: the Ext fields (packet boundaries of the top design plus library items) are not related to frozen items here; the deployed Ops instance is not shown to satisfy Bound.
2. AspisR1PublicPreparation (PRVEq_PP_l4.lean, PCVL_L007): all 26 definitions of the fresh PCVL_E003 emission (semantic_validated, begin, public_transcript, sample_block_validated, Prefix.record/validated_record, ValidatedRecord accessors, the sampler loops and qm31_sample, the SemanticTranscript.new and closure instances, DOMAIN, and aspis_core P, CM31.new, QM31.ZERO) equal the gate constants. aspis_core P/CM31.new/QM31.ZERO are now transparent (PCVL_E003) and equal the gate values. CONDITIONAL_ON_BINDING on two callees that resolve to the gate by name: pool_v1 Public.public_bytes (Aspis; extraction failed twice, retired) and core.result.Result.map_err (HM-C).
3. Earlier PRVEq_PP_l1.lean (PCVL_L001, exit 0, 23 definitions) bound P and QM31.ZERO by `ok <gate value>`; superseded by claim 2 for those.

## Naming vs not naming (PublicPreparation)
Naming only: Digest32 path, Challenges path (gate r1_wire.Challenges is the probe crate's copy; fields identical), aspis_statement.pool_v1 prefix, one parenthesization. Not naming: P/ZERO/CM31.new were external axioms (Result-typed) in the first emission; resolved by extraction, not by renaming.

## Failed shapes
PCVL_L002, L003 (VTop: missing carriers, then application without parentheses); PCVL_L005, L006 (stage-1 rfl timeout on semantic_validated and begin; L007 pins stage 2); PCVL_E001 (tool bug), E002 and E004 (public_bytes, Aeneas), see classifications. Failed probe sources kept; none contains sorry.

## Not done
stage1/2_owned, tx1, prepare (sibling PCVK_); relating the VTop Ext fields to frozen items; public_bytes. See PCVL_REMAINING.json.
