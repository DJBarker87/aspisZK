# PCA direct children

All direct children remain OPEN here. Zero Stream A roots are instantiated; direct source calls map to Pool rows, with any shared descendants owned by Stream A. No NLG caller clause is silently discharged. This inventory is not E5 closure.

| Row | Class | Source occurrences | Owner | Packet status |
|---|---|---|---|---|
| POOL:309 decode_pair_forest_deposit_instruction_v1 | B | 995 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:313 decode_terminal_master_box_v1 | B | 1006 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:165 pool_v1_note_commitment | A | 1007 | PCB_ | OPEN |
| POOL:199 pool_v1_pair_forest_deposit_lane_v1 | B | 1013 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:304 decode_deposit_lane_box_v1 | B | 1018 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:222 single_output | B | 1022 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:220 leaf_digest | B | 1023 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:326 prepare_deposit_append_v1 | B | 1025 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:246 root_history_location | A | 1027,1028 | PCB_ | OPEN |
| POOL:301 account_is_zeroed_program_page | D | 1032 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:280 pool_v1_root_page_address | A | 1034,1062 | PCB_ | OPEN |
| POOL:362 plan_fresh_program_pda | D | 1035,1063 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:340 validate_lane_current_page | D | 1048,1056 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:332 require_exact_account_count | B | 1080 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:367 require_unique_accounts | D | 1081 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:365 require_token_program_account | B | 1083 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:388 plan_legacy_deposit_transfer_from_identity_v1 | D | 1084 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:382 exact_transfer_account_infos_v1 | D | 1091 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:364 require_payer_and_system_program | B | 1097,1135 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:358 create_or_allocate_pda | B | 1107,1145 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:333 require_program_owned_zeroed | D | 1117,1155 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:395 validate_exact_deposit_delta_v1 | D | 1171 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:286 write_new_page_unchecked | B | 1175,1187 | unassigned child packet; PCA parent interface only | OPEN |
| POOL:279 append_roots_unchecked | A | 1183 | PCB_ | OPEN |

Std/SDK operations (no Pool row under (au)/(be)): accounts.get (997/1000/1003/1060); slice/index (1082/1095/1096/1132–1134); data_is_empty (1031); parent try_borrow_mut_data (1168/1169), guard deref and reverse lexical drop; to_le_bytes and seed slice construction; lane copy_from_slice (1173). Thin wrappers reuse NLF only within their actual domain; native call-site association and explicit child loan schedules remain open.

Runtime boundaries: token CPI at 1170 through the deployed runtime and SDK down to sol_invoke_signed; system CPI occurrences inside create_or_allocate_pda at source call sites 1107/1145, including transfer/create/allocate/assign branches of its rent child. Their exact nested occurrence inventory remains to be completed; no CPI bridge is claimed. PDA op38 stays quantified, with exact seed/program/status/frame forwarding required. RuntimeCpiReadonlyEntry7 unused.

PCB branch read-only inventory at Stage 1 contained only its handoff/ledger placeholders, no RowSpec/root module. These four first targets remain dependencies: POOL:165/246/279/280. Other class-A targets also belong to PCB, never duplicated here.
