# NLX remaining obligations

Target not yet established. 40/40 Lean/link/audit scopes;0Kani/0extraction. No further ledger-only replay closes these rows. Existing Lean-only folds belong to the named live jobs; new native segments/controls require their Kani authority under(bg), which this job does not have.

## crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:087 | prepare | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:137. | NLR_ tx1-observed |
| TX1:094 | tx1 | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:087. | NLV_ tx1-top |
| TX2:064 | tx2_authenticated | Actual authenticated parent continuation; discharge065 own original-input extents and Root0/root1 checkpoint/proof provenance with persistence AND proof-digest/writer binding; full native/account/SDK/allocator/copy segments and every Result/error/abort/frame under(bg). NLM remains support only. | NLW_ tx2-entry3; ruling(bg) |

## crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:136 | verify_finish | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. | NLU_ tx1-finish2 |
| TX1:137 | verify_observed | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:136. | NLR_ tx1-observed |

## programs/r1-cost-probe/src/lib.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:328 | first_decoded | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:094. | NLQ_ tx1-entry2 |
| TX1:330 | process_r1_cost_probe_instruction | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:333. | NLQ_ tx1-entry2 |
| TX2:213 | process_r1_cost_probe_instruction | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:221. | NLW_ tx2-entry3; ruling(bg) |

## programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:333 | process | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:344. | NLQ_ tx1-entry2 |
| TX2:217 | decode_lane_from_pool_release | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. | UNOWNED; paused by lead, resume under(bg) |
| TX2:221 | process | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:240. | NLW_ tx2-entry3; ruling(bg) |

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:344 | stage1 | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:345. | NLQ_ tx1-entry2 |
| TX1:345 | stage1_owned | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:328. | NLQ_ tx1-entry2 |
| TX2:233 | authenticate_asq8_accounts | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:217, TX2:234. | UNOWNED; paused by lead, resume under(bg) |
| TX2:234 | authenticate_invariant_release_registry | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. | UNOWNED; paused by lead, resume under(bg) |
| TX2:240 | stage2 | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:241. | NLW_ tx2-entry3; ruling(bg) |
| TX2:241 | stage2_owned | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:064, TX2:242. | NLW_ tx2-entry3; ruling(bg) |
| TX2:242 | validate_asq8 | Complete frozen entry/adapter transcription under(bg), native call-boundary segments with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:233. | UNOWNED; paused by lead, resume under(bg) |

Pool.prefix_to_cpi, NIB-P1/P2/P3/P4 and POOL.read_to_settlement all remain OPEN; exact member/status tables are in NLX_PHYSICAL.md. All3 ON guard owners and3 OFF review owners remain OPEN. PCE15 CLOSED helpers are read-only context, no Pool promotion. K086 reachability/exclusion, owner(aj)(a), L187 cold release replay/L188 artifact/extraction association and NKT-F2/F3 provenance remain. No remaining job-owned mathematical theorem is hidden behind Kani exhaustion; this refresh has no owned native function work and does not duplicate live owner work.
