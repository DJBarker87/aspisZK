# PCVS_ HANDOFF: phase P3r (E32 and the remaining tx2 slots)

Target not yet established. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Nothing pushed or merged; no ledger, trust, RSL, contract or shipped source changed; no trust row added. 14 of 40 Lean host scopes, 2 of 6 extraction scopes, one at a time, caps unraised, swap 0 (PCVS_SCOPES.json, PCVS_ATTEMPTS.jsonl, receipts PCVS_Lnnn/, PCVS_Ennn/).

## Difference at a matching configuration
None found. The E32 route compares the frozen WideExact::from_le_bytes (through op2) with decode_e_spec on all 32-byte windows, including non-canonical limbs and both rejection paths; they agree.

## Closed (exit 0, standard axioms only; PCVS_STATUS.json)
1. E32: PCVS_E32.e32_core (PRVEq_E32_s4, L005); deployed_tx2_common_s and deployed_tx2_authenticated_s (PRVEq_Tx2Deployed_s1, L006) have no hE. Remaining parameters are the deployed stage dictionaries (reserved, query, geo, base, finish) at inact := NJC_ClosedCalls.inactive, mk := NHV_ReleaseOps.mark.
2. op17 bindings: frozen WideExact mul/ZERO/ONE (extraction PCVS_E001, ON) equal the gate (PRVEq_WideBind_s2, L008); op17_frozen_bound (PRVEq_Op17_s2, L010) takes the frozen callees, no binding hypothesis. Gate ONE is related.
3. Helpers: frozen tag, final_len, checkpoint_size, CHECKPOINT_FIXED (extraction PCVS_E002, ON) equal the deployed yDep values; QM31::ZERO equals zeroK (PRVEq_CkptSmall_s4, L014). Composition deployed_tx2_common_m/authenticated_m (PRVEq_Tx2Deployed_s2, L015) with those four externals frozen.

## Plainly: what is only organisation
Slots op5, op6, op9, op10, op19 (and op11), read_checkpoint_*, QM31::from_le_bytes, heap::filled are still instantiated by deployed fields and related to no frozen item (PCVS_UNRELATED.json). yMix = yDep is proved; deployed_tx2_*_m restates the same theorem and its gain is the four proved field relations only.

## Not done
op5/op6/op9/op10/op19 and the stage2 adapter slots (item 4): not started; each needs a frozen emission (BatchedWeights uses Vec, library rows) and a relation across hand-adapted bodies. QM31::from_le_bytes needs a 16-byte-window theorem of the E32 form (deployed decode_k_spec has no length check). Next deliverable: that theorem, then read_checkpoint_* extraction.
