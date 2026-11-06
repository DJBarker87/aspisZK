# Pool composition status

Target not yet established. These are conservative source-inventory dependencies, not a proved physical callgraph. The15 closed helper bodies do not establish a parent producer, a guard owner, same-execution composition, privacy or the100-bit per-attempt target. All119 shared bodies retain ledger23 ownership; SAME argument/caller clauses must be proved by each Pool caller.

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
