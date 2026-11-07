# PCD real call dependencies

This table follows the frozen source. PCD_CONSERVATIVE_CHILDREN.md preserves the initial MIR name-alternative inventory; generic `::new` alternatives are NOT call edges and never block a row.

No result is promoted by this table. Every callee use must be instantiated at SAME arguments.

## POOL:311 decode_terminal_checkpoint_box_v1
- POOL:310 (D) decode_retained_pair_forest_checkpoint_account_v1 — OPEN Pool child / native packet required

## POOL:312 decode_terminal_lane_box_v1
- POOL:306 (D) decode_lane_account_from_program_invariant_v1 — OPEN Pool child / native packet required

## POOL:313 decode_terminal_master_box_v1
- POOL:307 (D) decode_master_account — OPEN Pool child / native packet required

## POOL:314 decode_terminal_request_box_v1
- POOL:207 (B) decode_pool_v1_pair_forest_terminal_request_v1 — Stream A CLOSED packet; exact own-argument domain still required

## POOL:319 next_lane_image_box_v1
- POOL:320 (B) next_pair_forest_lane_v1 — PCD CLOSED under (ah)/(ay)(3); exact full native/model/gate packet in PCD_CLOSED.json
- POOL:315 (B) encode_lane_from_authenticated_result_v1 — OPEN Pool child / native packet required

## POOL:320 next_pair_forest_lane_v1
- POOL:278 (A) from — OPEN Pool child / native packet required

## POOL:339 validate_authenticated_terminal_result_v1
- POOL:336 (B) terminal_common_box_v1 — OPEN Pool child / native packet required
- POOL:338 (B) transfer_terminal_statement_box_v1 — OPEN Pool child / native packet required
- POOL:342 (B) withdrawal_terminal_statement_box_v1 — OPEN Pool child / native packet required
- POOL:213 (B) validate_pool_v1_pair_forest_terminal_result_against_statement_v1 — Stream A CLOSED packet; exact own-argument domain still required

## POOL:350 plan_pair_forest_terminal_dispatch_with_bytes_v1
- POOL:351 (B) proof_transport_verifier — OPEN Pool child / native packet required
- POOL:353 (B) require_verifier_program — OPEN Pool child / native packet required
- POOL:352 (D) require_checkpoint_distinct — OPEN Pool child / native packet required
- POOL:372 (D) authenticate_verifier_selection_v1 — OPEN Pool child / native packet required
- POOL:370 (A) matches — OPEN Pool child / native packet required
- POOL:371 (A) matches_verifier_owner — OPEN Pool child / native packet required

## POOL:347 dispatch_pair_forest_terminal_readonly_v1
- POOL:349 (B) plan_pair_forest_terminal_dispatch_v1 — OPEN Pool child / native packet required
- POOL:348 (D) invoke_pair_forest_terminal_with_runtime_v1 — OPEN Pool child / native packet required

## POOL:348 invoke_pair_forest_terminal_with_runtime_v1
- POOL:353 (B) require_verifier_program — OPEN Pool child / native packet required
- POOL:351 (B) proof_transport_verifier — OPEN Pool child / native packet required
- POOL:352 (D) require_checkpoint_distinct — OPEN Pool child / native packet required
- POOL:344 (A) clear_return_data — PCB-owned; typed PCD target drafted; instantiate only after merged root
- POOL:346 (B) invoke — OPEN Pool child / native packet required
- POOL:345 (A) get_return_data — PCB-owned; typed PCD target drafted; instantiate only after merged root
- POOL:208 (B) decode_pool_v1_pair_forest_terminal_result_v1 — OPEN Pool child / native packet required

## Standard operations
Box allocation, scalar checked addition, raw fixed-array comparison, iteration, Vec/Rc operations and cleanup execute in the appropriate native cut under (au), the exact KMX rule and std/allocator trust. They are not extra child rows. Abort/cleanup prefixes are still obligations.

## Closed constituents
POOL:314 and POOL:320 passed the final Stream C gate. The former consumes the CLOSED NLO decoder at SAME bytes; the latter executes every reached frozen error-conversion arm natively, without re-owning278. No open helper is assumed as a callee packet.

## Shared findings
The three boxed account decoders need the actual current-state SDK/decoder packets (306/307/310), not three new runtime success assumptions. POOL:319 also needs the deployed 315 encoder; POOL:339 needs the three actual Box statement constructors. These are recorded once here; no wrapper assumes them CLOSED.

POOL:314 has a CLOSED shared decoder but still needs its OWN complete native forwarding/Box/abort/frame certificate. It is independent of the account decoders and is next after the first complete row. POOL:350 depends on actual registry authentication 372. POOL:347 includes 349, not merely 350. POOL:348 includes 346 and the PCB runtime wrappers; its passed-cell effect remains unconstrained.
