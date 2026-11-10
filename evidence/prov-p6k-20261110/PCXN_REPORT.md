# PCXN_ (P6k): recount v2 with the retroactive transcription rule and the consolidated CANNOT_EXTRACT table

Script work on the Mac, 0 Lean, 0 extraction, 0 host scopes. Reads research at 6c8f7bb1b3d (pinned at run start). Frozen 4bb3b3f. No ledger row, trust row, RSL or contract touched.

**Reproduction first.** PCXL_ chain reproduced exactly (assert): 1150 / 420 / 137, 122 of 599 rows.

**Overlays, each with its delta** (settled / not settled / other, rows):
- O1 (decision 1) HAND_ADAPTED 5 + NO_FROZEN_COUNTERPART 3 count not settled: 1150/428/129, rows 122 (matches the lead's expected figure).
- Merged on research after d80d89716a0: P5f (PCWP_) +2 settled, -14 not settled, +12 other (12 DEPENDS_ON_LIBRARY_TRUST via HM-D) -> 1152/414/141; P5h (PCWR_) +7 settled (Qm31SamplerIndex, superseding 7 conditionals), -5 not settled, -2 other -> 1159/409/139. P6j (PCXM_) adds no class map; no adapter. Rows unchanged at 122.
- O2 (decision 2): 32 keys -> OPEN_TRANSCRIPTION (all RECEIPTED_PIN_EQUAL): 1127/441/139, rows 122. Rule: a key moves iff it is a function key or item-specific key of one of the 51 Aspis-code items of PCXM table1 and its class is a settled class that is not a fresh = gate proof (RECEIPTED_PIN_EQUAL, RECEIPTED_SELECTED_MASK_PROBE); fresh = gate classes keep their class. NKM-RTNGB006 is treated as not discharged (its key stays EQUALITY_PROVED by a fresh = gate proof, no count effect). Without P5f/P5h the same overlays give 1118/460/129.

**Result: settled 1127 / not settled 441 / other 139 of 1707; rows settled-only 122 of 599.**
- Settled: EQUALITY_PROVED 920, EQUALITY_PROVED_JOB 67, EQUALITY_PROVED_P1N 13, OFF_EMISSION_WRAPPING_ACCEPTED 22, RECEIPTED_PIN_EQUAL 67, RECEIPTED_SELECTED_MASK_PROBE 38.
- Not settled: OPEN 327, OPEN_NOT_REDERIVABLE 40, RECEIPTED_TEXT_DIFFERS 34, OPEN_TRANSCRIPTION 32, HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 3.
- Other: TYPE_ISOMORPHISM 45, CONDITIONAL_ON_BINDING 48, DEPENDS_ON_LIBRARY_TRUST 24, GATE_ONLY_HELPER 8, EQUALITY_DOMAIN 7, REFINEMENT_LOOP_RETURN 4, REFINEMENT_THROUGH_TYPE_MAP 3.

**Rows blocked by OPEN_TRANSCRIPTION keys:** alone 0, among other blockers 20 (the 32 reclassified keys touch 20 rows, all already blocked; so O2 costs no settled-only row). Over all keys mapped to the 51 items (178 keys, 111 unsettled): alone 1 (TX2:217), among 67.

**Rows blocked by the CANNOT_EXTRACT set:** alone 6 (TX1:132, TX1:135, TX1:277, TX1:284, TX2:171, TX2:226), among other blockers 123 (129 rows touched). Set = 65 cone keys (56 unsettled): the 41 of PCXM Table 2 (PCXM's 6/123 reproduced) plus 24 added from PCWL/PCWM cause CANNOT_EXTRACT (CurrentClaimSumModel, S1 owned_* copies); the 24 touch no further row. OT and CE together: alone 6, among 130.

**Items still UNMAPPED** (no cone function key and no item-specific key): 30 of 51: NJY-RT149/152/153/201/203, NJZ-RT189/201/202/203/204, NKJ-RT036/040/041/043/044, NKI-RT234, NKY-RT216/218/235, NKR-RT-220/225/250/251, the six POOL items, and the withdrawn public_bytes item. They have item records but cannot move a key.

**CANNOT_EXTRACT table** (PCXN_CANNOT_EXTRACT.json): 21 entries with exact tool error, tool version, evidence path, cone keys, rows, from PCWH, PCWO, PCVX, PCVV, PCWL, PCWM, PCWN. Stage1 (TX1:344) and stage2 (TX2:240) are added with the guard-drop error (NJN_L001, InterpBorrows.ml:2731) and the NMV E1/E003/E004 failures; NJN_L001 extracted the SDK guard reference, not the frozen wrappers, which the entry says. public_bytes is removed. Entries with no cone key: stage1, stage2, op22, op48/49, verify_in_place, finish_relation, semantic_rounds, deployment_id, and the op21/op24 shape miss (a worker defect, not a tool limit).

**For the lead to confirm.** (a) The reading of "credited through the RT row rather than a fresh = gate proof" as the two RECEIPTED classes; the upper bound (every receipt-credited key of the items' own rows) is 103 keys against 32. (b) The 63 EQUALITY_PROVED keys in TX1:344/TX2:240-type item rows keep their class by the rule. (c) 3 RECEIPTED_PIN_EQUAL and 6 EQUALITY_PROVED keys sit inside the CE key set and are settled.

Target not yet established.
