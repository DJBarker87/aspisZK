# NLX physical association distances

Target not yet established. Seventeenth all-slices composition test. Counts are conditional native/source association obligations under NDT semantics, not runtime measurements or security bits. All599 rows and canonical edges are retained.

| Part | Total | CLOSED | OPEN | QUALIFIED |
|---|---:|---:|---:|---:|
| (ao)(3)(b) | 53 | 40 | 13 | 0 |
| (ao)(3)(c) | 546 | 541 | 5 | 0 |

## Shortest OPEN spine paths

BFS minimizes canonical call edges at the same ledger23 targets. Independent Dijkstra minimizes (OPEN rows, call edges), including entry row cost. CLOSED children do not close their parent; conservative069→202 is retained.

TX1: TX1:330 process_r1_cost_probe_instruction [OPEN] → TX1:333 process [OPEN] → TX1:344 stage1 [OPEN] → TX1:345 stage1_owned [OPEN] → TX1:328 first_decoded [OPEN] → TX1:094 tx1 [OPEN]. OPEN distance 6; 5 call edges. Independent minimum-OPEN search agrees.

TX2: TX2:213 process_r1_cost_probe_instruction [OPEN] → TX2:221 process [OPEN] → TX2:240 stage2 [OPEN] → TX2:241 stage2_owned [OPEN] → TX2:064 tx2_authenticated [OPEN] → TX2:065 tx2_common [CLOSED] → TX2:115 finish_relation [CLOSED]. OPEN distance 5; 6 call edges. Independent minimum-OPEN search agrees.

## OPEN rows by source file and owning live job

### crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Function | Owner |
|---|---|---|
| TX1:087 | prepare | NLR_ tx1-observed |
| TX1:094 | tx1 | NLV_ tx1-top |
| TX2:064 | tx2_authenticated | NLW_ tx2-entry3; ruling(bg) |

### crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Function | Owner |
|---|---|---|
| TX1:136 | verify_finish | NLU_ tx1-finish2 |
| TX1:137 | verify_observed | NLR_ tx1-observed |

### programs/r1-cost-probe/src/lib.rs

| Row | Function | Owner |
|---|---|---|
| TX1:328 | first_decoded | NLQ_ tx1-entry2 |
| TX1:330 | process_r1_cost_probe_instruction | NLQ_ tx1-entry2 |
| TX2:213 | process_r1_cost_probe_instruction | NLW_ tx2-entry3; ruling(bg) |

### programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Function | Owner |
|---|---|---|
| TX1:333 | process | NLQ_ tx1-entry2 |
| TX2:217 | decode_lane_from_pool_release | UNOWNED; paused by lead, resume under(bg) |
| TX2:221 | process | NLW_ tx2-entry3; ruling(bg) |

### programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Function | Owner |
|---|---|---|
| TX1:344 | stage1 | NLQ_ tx1-entry2 |
| TX1:345 | stage1_owned | NLQ_ tx1-entry2 |
| TX2:233 | authenticate_asq8_accounts | UNOWNED; paused by lead, resume under(bg) |
| TX2:234 | authenticate_invariant_release_registry | UNOWNED; paused by lead, resume under(bg) |
| TX2:240 | stage2 | NLW_ tx2-entry3; ruling(bg) |
| TX2:241 | stage2_owned | NLW_ tx2-entry3; ruling(bg) |
| TX2:242 | validate_asq8 | UNOWNED; paused by lead, resume under(bg) |

Unowned OPEN: TX2:217, TX2:233, TX2:234, TX2:242. These four adapter rows are paused by the lead; resume under(bg). TX1:094 belongs to NLV_; it is no longer listed as unowned. No sibling worktree was edited.

## Argument-domain boundary

TX2:065 uses only NLT_CompleteRoot.root; NLT_Root.root is permanently withdrawn for credit (NLT-F1). Both full resolved outcomes and the independent stopped-C04 prefix are retained. C01/C04/C07 are installed at SAME actual arguments. The three original-input clauses proof.val.length=57607, pub.val.length≤1880 and NLP_InputDomain.Root0 ck proof remain verbatim on OPEN TX2:064 (NLX_PARENT_CLAUSES.json). Root0/root1 cross-transaction checkpoint/proof provenance is not discharged by065, lengths or RuntimePersistence alone. No parent promotion follows. Other clause and inventory history is retained in NLX_CLAUSE_MATRIX.json.xz and the ledger.

## (ao)(3)(d) Pool named obligations: read-only Stream C context

Source: evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz, PCE_COMPOSITION.md and PCE_HANDOFF.md. No Pool promotion in this job. Pool397 ON =278 new +119 shared bodies;15/278 new helpers CLOSED,263 OPEN; all119 shared bodies retain Stream A ownership. Three ON guard owners OPEN; three OFF owners remain outside ON counts. Three held sites (two ON/one OFF) remain OPEN. Exact frozen Pool b936275465600469312d1f058cdc91ea2a11f3dc; ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; historical121f3e29 superseded. No verifier row depends on Pool ELF.

| Held site | Scope | Status |
|---|---|---|
| POOL:328 process_pair_forest_deposit_with_runtime_v1 | ON | OPEN: exact guarded transfer/CPI continuation |
| POOL:330 process_pair_forest_terminal_with_verifier_v1 | ON | OPEN: guarded terminal/marker and verifier/token continuation |
| POOL:400 process_pair_withdrawal_with_verifier_v1 | OFF review | OPEN; excluded from ON counts |

## NIB-P1

OPEN. Waiting on POOL:345, POOL:347, POOL:348. Closed helper bodies: POOL:344.

POOL:344 `programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::clear_return_data` — CLOSED.
POOL:345 `programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::get_return_data` — OPEN.
POOL:347 `programs/aspis-pool/src/pair_forest_dispatch.rs::dispatch_pair_forest_terminal_readonly_v1` — OPEN.
POOL:348 `programs/aspis-pool/src/pair_forest_dispatch.rs::invoke_pair_forest_terminal_with_runtime_v1` — OPEN.

## NIB-P2

OPEN. Waiting on POOL:311, POOL:312, POOL:313, POOL:314, POOL:339.

POOL:311 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_checkpoint_box_v1` — OPEN.
POOL:312 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_lane_box_v1` — OPEN.
POOL:313 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_master_box_v1` — OPEN.
POOL:314 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_request_box_v1` — OPEN.
POOL:339 `programs/aspis-pool/src/pair_forest.rs::validate_authenticated_terminal_result_v1` — OPEN.

## NIB-P3

OPEN. Waiting on POOL:319, POOL:320.

POOL:319 `programs/aspis-pool/src/pair_forest.rs::next_lane_image_box_v1` — OPEN.
POOL:320 `programs/aspis-pool/src/pair_forest.rs::next_pair_forest_lane_v1` — OPEN.

## NIB-P4

OPEN. Waiting on POOL:330.

POOL:330 `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` — OPEN.

## POOL.prefix_to_cpi

OPEN. Waiting on POOL:322, POOL:329, POOL:330, POOL:347, POOL:348, POOL:350.

POOL:322 `programs/aspis-pool/src/pair_forest.rs::plan_pair_forest_spend_layout_v1` — OPEN.
POOL:329 `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_v1` — OPEN.
POOL:330 `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` — OPEN.
POOL:347 `programs/aspis-pool/src/pair_forest_dispatch.rs::dispatch_pair_forest_terminal_readonly_v1` — OPEN.
POOL:348 `programs/aspis-pool/src/pair_forest_dispatch.rs::invoke_pair_forest_terminal_with_runtime_v1` — OPEN.
POOL:350 `programs/aspis-pool/src/pair_forest_dispatch.rs::plan_pair_forest_terminal_dispatch_with_bytes_v1` — OPEN.

## POOL.read_to_settlement

OPEN. Waiting on POOL:345, POOL:347, POOL:348, POOL:311, POOL:312, POOL:313, POOL:314, POOL:339, POOL:319, POOL:320, POOL:330. Closed helper bodies: POOL:344.

POOL:344 `programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::clear_return_data` — CLOSED.
POOL:345 `programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::get_return_data` — OPEN.
POOL:347 `programs/aspis-pool/src/pair_forest_dispatch.rs::dispatch_pair_forest_terminal_readonly_v1` — OPEN.
POOL:348 `programs/aspis-pool/src/pair_forest_dispatch.rs::invoke_pair_forest_terminal_with_runtime_v1` — OPEN.
POOL:311 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_checkpoint_box_v1` — OPEN.
POOL:312 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_lane_box_v1` — OPEN.
POOL:313 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_master_box_v1` — OPEN.
POOL:314 `programs/aspis-pool/src/pair_forest.rs::decode_terminal_request_box_v1` — OPEN.
POOL:339 `programs/aspis-pool/src/pair_forest.rs::validate_authenticated_terminal_result_v1` — OPEN.
POOL:319 `programs/aspis-pool/src/pair_forest.rs::next_lane_image_box_v1` — OPEN.
POOL:320 `programs/aspis-pool/src/pair_forest.rs::next_pair_forest_lane_v1` — OPEN.
POOL:330 `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` — OPEN.

## Six guard owners

Three ON owners remain OPEN; three OFF owners stay in review and do not enter397 ON or278 new counts. No original full owner scope was re-run.

- POOL:328 (ON), OPEN: `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1`. Packet: exact_transfer_account_infos_v1; deployed SolanaPoolCpiRuntimeV1::invoke. Direct open child rows: POOL:004, POOL:006, POOL:008, POOL:009, POOL:010, POOL:011, POOL:012, POOL:014, POOL:042, POOL:074, POOL:075, POOL:079, POOL:085, POOL:091, POOL:094, POOL:096, POOL:107, POOL:108, POOL:112, POOL:113, POOL:115, POOL:116, POOL:118, POOL:121, POOL:122, POOL:124, POOL:125, POOL:141, POOL:142, POOL:144, POOL:147, POOL:148, POOL:149, POOL:154, POOL:155, POOL:156, POOL:158, POOL:159, POOL:160, POOL:165, POOL:189, POOL:199, POOL:220, POOL:222, POOL:223, POOL:241, POOL:274, POOL:275, POOL:276, POOL:279, POOL:280, POOL:286, POOL:287, POOL:288, POOL:299, POOL:301, POOL:304, POOL:309, POOL:313, POOL:326, POOL:332, POOL:333, POOL:340, POOL:346, POOL:356, POOL:358, POOL:362, POOL:364, POOL:365, POOL:367, POOL:382, POOL:388, POOL:395, POOL:397.
- POOL:330 (ON), OPEN: `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1`. Packet: plan_pair_forest_spend_layout_v1; exact_withdrawal_transfer_account_infos_v1; deployed verify/settle instantiations. Direct open child rows: POOL:002, POOL:004, POOL:006, POOL:014, POOL:042, POOL:074, POOL:075, POOL:079, POOL:085, POOL:091, POOL:094, POOL:096, POOL:107, POOL:108, POOL:110, POOL:113, POOL:117, POOL:118, POOL:121, POOL:124, POOL:141, POOL:142, POOL:144, POOL:148, POOL:149, POOL:155, POOL:156, POOL:158, POOL:241, POOL:279, POOL:286, POOL:288, POOL:289, POOL:294, POOL:311, POOL:312, POOL:313, POOL:314, POOL:319, POOL:322, POOL:334, POOL:337, POOL:339, POOL:341, POOL:347, POOL:357, POOL:361, POOL:364, POOL:365, POOL:383, POOL:389, POOL:396.
- POOL:398 (OFF), OPEN: `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1`. Packet: prepare_fresh_program_pda; actual retained lane-guard loop. Complete original owner bridge remains absent.
- POOL:327 (ON), OPEN: `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1`. Packet: prepare_fresh_program_pda; decode/encode checkpoint and persistence suffix. Direct open child rows: POOL:004, POOL:006, POOL:014, POOL:042, POOL:074, POOL:075, POOL:079, POOL:085, POOL:091, POOL:094, POOL:096, POOL:107, POOL:108, POOL:113, POOL:118, POOL:121, POOL:124, POOL:141, POOL:142, POOL:144, POOL:148, POOL:149, POOL:155, POOL:156, POOL:158, POOL:241, POOL:288, POOL:308, POOL:321, POOL:332, POOL:333, POOL:358, POOL:362, POOL:364, POOL:367.
- POOL:399 (OFF), OPEN: `programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1`. Packet: deployed verifier invocation; apply_pair_private_transfer_after_state_v1. Complete original owner bridge remains absent.
- POOL:400 (OFF), OPEN: `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1`. Packet: require_unique; exact_withdrawal_transfer_account_infos_v1; marker/verification/token children. Complete original owner bridge remains absent.

## Trust and carrier boundaries

RuntimeCpiAccountView (ADDED-LEAD-20261110) is required by open328/330 continuations: excluded keys retain data/lamports/owner; passed keys reflect callee final values. Exact metas/infos, uniqueness-to-cell separation, SDK guard counters/handles and every continuation remain caller obligations. No closed PCE row uses that new runtime row. It supplies neither CPI success nor token/system-program semantics. RuntimeCpiReadonlyEntry7 remains PENDING and unused.

ProgramError ABI abstraction is allowed only after the per-row entrypoint/propagation transcription in(c-b); no such new bridge is claimed here. Ordered error-path log/return-data effects remain exact obligations; any abstraction is SOUNDNESS-ONLY and never privacy evidence. Shared body records are conservatively SOUNDNESS-ONLY because Pool occurrence effects are not established.

PCA47 roots remain intermediate support, not a328 owner root. Existing NIB-P1..P4/read-to-settlement conditional model results are retained as conditional; new frozen Pool source receives no unvalidated historical closure. PCC owns328; PCD owns terminal P1..P3; consume their future packets at SAME arguments, never duplicate live work.

Frozen3, L154 statement parameter, narrowed D188/P6 option-A reclassification, RuntimePersistence data-only, privacy, two transactions and100-bit PER-ATTEMPT remain unchanged. Digest/error slots43/44; PDA38 quantified. Owner(aj)(a), final release replay/artifact and full Pool consumer association remain open.

## Status and trust inventory

K086: NHP_K086 core::cell::panic_already_mutably_borrowed::do_panic::runtime, core/cell.rs:898; unsupported runtime-formatted panic,1/1024failed,12unreachable. Liveness/abort; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING: same-game Pool settlement optionA versus conditional external Pool association optionB.

RuntimeCpiAccountView ADDED-LEAD-20261110 is carried under(c-a), soundness-side only: on a returning Pool CPI, keys absent from metas retain data/length/lamports/owner; passed keys in metas reflect callee final values. Exact metas/infos, cell separation and SDK counters/handles remain obligations. It gives no CPI success, token/system semantics, rollback, rent or readonly entry. RuntimeCpiReadonlyEntry7 PENDING/UNUSED. Extraction trust narrowing(bc) is a RECLASSIFICATION, not removal: post-loop explicit return/? exits need pattern exclusion or native exit certification. All prior trust retained; no cryptographic row changed. RuntimePersistence is data-only; initial Pool admission seven fields only; digest/error43/44, quantified PDA38; L154 statement parameter, frozen3, narrowedD188 and100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged.
