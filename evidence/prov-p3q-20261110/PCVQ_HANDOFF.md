# PCVQ_ HANDOFF: phase P3q (h18 and the deployed tx2 theorems)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p3q-20261110 (base ad97a498eb5). Lean scopes 25/45, extraction 0/6, one at a time, caps 6G/8G unraised, swap 0; verified (exit 0) scopes: L015, L021, L023, L024, L025 (plus probes L001, L016).

## Difference at a matching configuration
None. The fresh text (overflow ON) subtracts with a checked `-` where Port4A_NativeReader uses Usize.wrapping_sub; proved equal under 32 <= len (sub32), which follows from the checkpoint-size check.

## Proved (exit 0, standard axioms; see PCVQ_STATUS.json)
- resume_sim (PRVEq_Resume_q13): fresh VTop resume x = Port4A_NativeReader.resume ops, modulo the nominal error map, given Leaves x ops, all variants, all inputs.
- Leaves discharged for the deployed instance: any (anyLoop_eq), raw (rfl), k, filled, validate (fresh loop, PRVEq_Validate_q2), size/tag/final/ne/zero/sem/weights by definition of yDep.
- h18 and deployed_tx2_common_q / deployed_tx2_authenticated_q (PRVEq_Tx2Deployed_q6) under the single hypothesis E32 (op2 versus decode_e_spec on 32-byte windows).
- Item 5: ReviewedTranscription for the derives (PRVEq_DeriveRef_q1, PCVQ_ROW_DERIVE.md).

## Plainly: what is only organisation
yDep installs deployed values for thirteen Ext fields; the Bound conclusion therefore holds for externals that are the deployed ones, and none of those is related to its frozen item (PCVQ_UNRELATED.json). Slots op5/6/9/10/11/19 remain instantiated by deployed fields only.

## Not done
E32; items 2, 3, 4 (no extraction run). Next: E32 via the candidate-parser route recorded in PCVQ_UNRELATED.json.
