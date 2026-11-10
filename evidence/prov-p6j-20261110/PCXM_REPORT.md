# PCXM_ (P6j) exposure table: ReviewedTranscription (Aspis code) and CANNOT_EXTRACT

COUNTS (baseline at research d80d89716a0: 1150 settled / 420 not settled / 137 other of 1707 keys; 122 of 599 rows settled-only; all 420 not-settled keys settled gives 257). Tool used: PCXL_recount.rows_settled_only_if. "Alone" = rows that become settled-only if every key of the set were SETTLED and nothing else changed (gain over 122). "Among" = rows that contain an unsettled key of the set but stay blocked by other keys.

| Set | keys in cone (unsettled) | (a) blocked by these ALONE | (b) blocked AMONG others | rows if set + other-class keys sharing its rows also settled |
|---|---|---|---|---|
| CANNOT_EXTRACT set (Table 2, 41 keys) | 41 (32) | **6** | **123** (129 rows touched) | 163 (+41) |
| ReviewedTranscription not-discharged, item-specific keys (177 keys) | 177 (79) | **1** | **67** (68 touched) | 158 (+36) |
| ReviewedTranscription, function-name keys only (lower bound, 38 keys) | 38 (31) | 0 | 64 (64 touched) | 157 (+35) |
| ReviewedTranscription, all keys of the items' own rows (upper bound, 557 keys) | 557 (550) | 332 | 86 (418 touched) | 454 (+332) |
| UNION, item-specific + CE (214 keys) | 214 (107) | **7** | **156** (163 touched) | 164 (+42) |
| UNION, function-name + CE (76 keys) | 76 (60) | 6 | 157 (163 touched) | 163 (+41) |

Reading: the two sets are almost entirely blocked by other things. Settling every key of both, and nothing else, frees 7 rows (6 by CE alone, 1 by RT alone); settling also the other-class keys (CONDITIONAL_ON_BINDING, TYPE_ISOMORPHISM, etc.) in the touched rows frees 42 more (164 rows total). The "upper bound" row counts every definition in the item's own ledger rows, which for stage1 (TX1:344, 1228 keys) and stage2 (TX2:240, 674 keys) is almost the whole closure; it is not an item-specific figure.

Rows whose proofs rely on a ReviewedTranscription row at all (trust reach, any provenance status): own/direct consumers 64 of 599 (63 for not-discharged items); with call-graph callers (canonical_callees closure, an upper bound for "relies") 76 (75 not-discharged). The 6 POOL items have 0 (Pool rows are not among the 599).

Items: 51 Aspis-code (49 in NPI_TRUST_REACH plus public_bytes WITHDRAWN and LaneDecode REFUSED), 2 std/SDK listed and excluded (FieldDerives, deployment_id/HM-A). 50 not discharged, 1 discharged by key class (NKM-RTNGB006, secure_circle_point_from_parameter: gate key EQUALITY_PROVED; item-specific reference equality not separately evidenced). 35 Aspis-code items have no function key in the 1876-key universe (listed UNMAPPED in the JSON under unmapped_items_no_function_key; they still have row-based keys).

## Table 1 in brief (full per-item records in PCXM_EXPOSURE.json table1)
Group (items) | reached in L187 cones | state
- NJY decoders (decode_pool_identity_v1, checkpoint_v1, master_v1, registry entry/registry; 5), NJZ (echeck, tree_parent, default/empty/empty_roots; 5), NKJ qm31_sum_products family (5), NKY box decoders and levels (3), NKR copy/semantic terminal (6, two with OPEN keys), NKI-RT234: UNREACHED (YES for NKI-RT234/260, NKR-232) | no fresh emission key: NOT_YET_ATTEMPTED at gate-key level, except raw decoders master/checkpoint (IN_CANNOT_EXTRACT, PCVX E007/E008).
- NKM circle (3): UNREACHED; fn keys: NGB002 and NGB004 OPEN, NGB006 settled (discharged by key).
- NKI/NKL/NKU/NLH (semantic fold, composition_parts, terminal_parts, terminal_qm31, canonical_scan, resume, batch_tree/merkle): YES for most; fn keys exist and are OPEN (keys listed in JSON); ATTEMPTED, unsettled.
- stage1 TX1:344 and stage2 TX2:240 (bn, source fission): YES; no function key (the owned::stage1/stage2 gate keys are stage*_owned); 90 and 58 item-specific keys.
- decode_lane_from_pool_release TX2:217 (op50): YES; IN_CANNOT_EXTRACT (PCVV E007/E008, PCWH E007, PCWO E001 contexts mismatch after patch A). LaneDecode row REFUSED; same function.
- prepared_claim TX1:193/179/186 and queries_from_pairs TX1:168 (queries_from_pairs flagged via its Prepared::new callee only): YES; prepared_claim IN_CANNOT_EXTRACT (nested-loop returns), 3 OPEN CurrentClaimDot keys.
- polynomial TX2:119: YES; 1 OPEN function key (FIn_reference.polynomial).
- POOL324/345/296/320/223/332: UNREACHED; Pool code, not among the 599; no key mapping (UNMAPPED); NOT_YET_ATTEMPTED.
- public_bytes: withdrawn; PCWN item1 proves fresh = gate (PRVEq_PB_w3.lean, PCWN_L004) with no row, so it leaves CANNOT_EXTRACT; no key in the universe (UNMAPPED).

## Table 2 in brief (cone keys by gate module|definition and rows reaching them in the JSON table2)
op50 (1 key NCV_Reference.decode_lane_ref RECEIPTED_TEXT_DIFFERS; row TX2:217; 9 rows reach it); verify_in_place (UNMAPPED, no key); Prepared::new/prepared_claim (3 OPEN; 17 rows) plus CurrentClaimDotModel six (6 OPEN; 17 rows); decode_k (4 OPEN; 31 rows); tx2_authenticated and tx2_common (1 CONDITIONAL each; 3 rows); mark (1 settled; 4 rows); query_loop op6 (3 RECEIPTED_PIN_EQUAL; 86 rows); query_values (2; 93 rows); finish_relation op19 (UNMAPPED); semantic_boundary (4 OPEN; 21 rows), claims (3 OPEN; 25 rows), semantic_rounds (UNMAPPED), AspisR1SemanticCallExtraction eight (8 OPEN; rows in JSON); require_distinct_accounts (4 OPEN; 16 rows); raw decoders op48/op49 and op22 (UNMAPPED, no cone key); other aspis_statement decoders by name match decode_pool_v1* (7 keys, 3 OPEN; 32 rows, name match only).

Method limits. Keys come from name matching of the frozen function to gate definitions (stem-checked, shown in match_how) and from the rows' own definition lists (PCXF row tables via PCXL); "item-specific" keys are keys of the item's own rows reached by no row outside the union of the RT-relying rows. These are mechanical estimates, not a proof of which definitions discharge an item. Discharge here is by key class (STATUS classes in PCXL), not by item-specific theorem citation; STATUS file hits per item are in table1.status_file_hits. Nothing was changed in ledger, trust rows, RSL or contract.

Target not yet established.
