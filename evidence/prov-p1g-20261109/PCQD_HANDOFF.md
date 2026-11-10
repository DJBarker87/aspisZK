# PCQD_ HANDOFF: phase P1g (frozen extractions for the non-frozen cone modules)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no equality proof written. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p1g-20261109/. 38 of 40 extraction scopes (PCQD_E001-E038), 0 Lean, one at a time, caps 3G/4G, swap 0, 180 s unraised. 11 runs exit 0, 27 failed or timed out (PCQD_FAILURES.json). Receipts PCQD_Exxx/receipt.json, PCQD_ATTEMPTS.jsonl, PCQD_RECEIPT_SUMMARY.json.

## Priority item: r0.transport.order
A fresh frozen extraction exists: PCQE_E001 (P1d), original Aeneas 959659a6, overflow ON, features r0, 4bb3b3f (order, order_loop0, order_loop0.body, order_loop0_loop0, order_loop0_loop0.body). PCQD_E006 tried the extended Aeneas once: Not_found, so no extended emission. See priority_r0_transport_order in PCQD_COVERAGE.json. Presence only; not compared with the gate.

## Tools and configuration
Extended Aeneas first, original 959659a6 after an extended failure of the same spec (PCQD_TOOLS.json, tool and sha256 in every PINS and in PCQD_COVERAGE.json). Every run overflow checks ON; basis in PCQD_CLASSIFICATIONS.json PCQD-C2 (P3b required ON for all 130 entries; I did not rescan gate module text).

## Result (PCQD_COVERAGE.json, name level over the 130 entries)
FRESH_PRESENT_PCQD 70, ALREADY_COVERED 12, NO_FROZEN_COUNTERPART 4, NOT_OBTAINED 44.
* Obtained: first_decoded, observer, OwnedAccount::data_len, require_verifier_checkpoint (E027, extended); AdapterReconstruct asq8_common, reconstruct_asq8_statement, transfer/withdrawal_statement_box (E003, ORIGINAL; extended Not_found E002); fast_domain tables/table_value/fibre_point/line_node (E010); D07 (E011, verifier for_range/batch_prefix_products) exited 0 but its emission carries only the types the coverage table lists as present, see NOT_OBTAINED for the function names; multiproof node_count and loops (E018); compact SEMANTIC_ROWS, compact_row, expand_semantic (E013, ORIGINAL); circle and field inverse chain (E024, E028); read_checkpoint_weights (E034); Variant::folds (E035); r1_wire payload/Error/SemanticTranscript (E036).
* NO_FROZEN_COUNTERPART (not run): decode_k_value, r24_canonical_mul.closure, NJT_claims_ref, candidate_claims.claims (frozen role: r1_semantic::claims, which failed on both tools). Four named PCVB candidate files do not exist in 4bb3b3f.
* Not obtained, with reasons (PCQD_FAILURES.json, CLASSIFICATIONS PCQD-C6/C7): require_distinct_accounts (nested-loop returns, both tools), decode_k loop, r1_semantic::claims, pair_forest_terminal and pair_tree_profile boxed decoders (original: memory growth to 3.26 GiB; extended: Unreachable, Not_found, name clash), candidate batch/query group, Prepared::new, BatchedWeights::new, QueryGeometry::for_range, batch_prefix_products, require_readonly_buffer/require_zero/readonly_buffer_meta_ok (Not_found), asq8_payment_reference (cfg aeneas_ref, shipped build lacks it; Charon fails even with the cfg). Hand-model obligations recorded in PCQD_HAND_MODELS.json (record only, no trust row).

## Caution
Name-level presence is not equality, and the original-Aeneas emissions (E003, E013) encode loops differently from the extended build most gate modules used (P2g). Loop-encoding differences are for P2/P3.

## Next
Two spare scopes. Open shapes worth one attempt each: require_readonly_buffer/require_zero as individual roots, Prepared::new with opaque callees, and a source-level split of the boxed decoders. Otherwise hand models.
