# PCVX_ HANDOFF: phase P3u (remaining adapter and tx2 slots)

Target not yet established. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No ledger row, trust row, RSL, contract or shipped source changed; no trust row added; nothing pushed or merged. Branch codex/pc-prov-p3u-20261110. Lean scopes 5 of 40 (L001-L005), extraction 13 of 14 (E001-E013), one at a time, caps unraised, swap 0, cargo jobs 4 (identity by class receipt PCWE_E003), rustc -Zthreads 1. Tables: PCVX_STATUS.json, PCVX_CANNOT_EXTRACT.json, PCVX_REMAINING.json, PCVX_CLASSIFICATIONS.json, PCVX_TOOLS.json, PCVX_ATTEMPTS.jsonl, receipts PCVX_Ennn/ PCVX_Lnnn/.

## Difference at a matching configuration
None found.

## Closed (exit 0, standard axioms only, no sorry, no raised heartbeats)
1. PRVEq_AspisR1TerminalDecoder_Funs_u1.lean (L003): fresh = gate for 87 definitions, including validate_pool_v1_pair_forest_terminal_statement_v1 and encode_pool_v1_pair_verified_afterstate_v1. Fresh text is the PCVX_E006 emission (aspis-statement crate, roots validate and encode afterstate, no opaque, original Aeneas, Charon 44 s total scope, Aeneas 3 s). This supersedes the P3t statement that op21/op24 had no frozen emission.
2. PRVEq_Slot24_u1.lean (L002): slot24, slot24_ok, slot24_err: deployed op24 = weak-Err map of the frozen encode emission, for every afterstate.
3. PRVEq_Slot21_u1.lean (L005): slot21, slot21_ok, slot21_err, slot21_on_decoded (on the NNH_S1DecodeOk domain): deployed op21 = weak-Err map of the frozen validate emission.
The only deviation from the emissions is the deployed model returning div where the emission returns Err (model-fidelity note K6, carried over). No hypotheses in slot21 and slot24; the _ok and _err forms take the emission value as hypothesis.

## Not closed
Raw aspis_statement decoders (op47/op48/op49/op51 hypotheses of the P3t slots): master and checkpoint decoders cannot be extracted (original Aeneas: Could not match the contexts at pair_forest_accounts.rs 295-298 and 463-482; extended crashes). Statement and afterstate decoders with the boxed decoder closure do not finish in Aeneas within 180 s (E001, E003, E004); the slowness is in the decoder closure, not Charon (Charon 49-63 s). The P3t hypotheses are unchanged.
op22 encode statement: cannot extract (Could not match the contexts, pair_forest_terminal.rs 318-324). op20 nullifier and op23 request decoder: emitted (E009), not related (type bridge to AdapterRw not built; generator found no common declarations against the hand model NMS_RequestModels). op16, op11, op53: not attempted.
tx2: op5 batch_merkle, op9 BatchedWeights::finish, op10 BatchedWeights::new now have frozen emissions (E012/E013; five P3s extractions had timed out at jobs 1), but are not related: the P2j NJS gate comparison shows ON-vs-OFF configuration differences in the batch key closure, which needs the gate configuration decision. op6 query_loop and op19 finish_relation cannot be extracted (Arrow types are not supported). deployed_tx2_common_t / authenticated_t are therefore unchanged from PCVU.

## Failed shapes
E001 (10 roots), E003 (Aeneas only on that LLBC), E004 (afterstate encode+decode): original Aeneas exit 124 at 180 s; shape class retired (whole decoder closure). E005, E008, E010: extended Aeneas crashes (exit 2). E002 spec-generator defect, E011 stager dest-file path (K1, K2). Lean: L001 (rw closed by rfl missing), L004 (namespace of LIB_Carriers); fixed, not shape retirements.

## Next deliverable
Extract op47/op51 decoders with opaque cuts (PCQF_E005 shape) and relate to the gate; the type bridge for op20/op23; the gate-configuration decision for op5/op9/op10; a source-refinement route or Aeneas change for the iter_mut().enumerate() loop (master/checkpoint/encode statement).
