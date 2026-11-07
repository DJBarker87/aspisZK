# NLX remaining obligations

Target not yet established. 40/40 Lean/link/audit scopes;0Kani/0extraction. No further ledger-only replay closes these rows. Existing Lean-only folds belong to the named live jobs; new native segments/controls require their Kani authority under(bj)/(bl), which this job does not have.

## crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:087 | prepare | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:137. | NMP_ tx1-observed3 |
| TX1:094 | tx1 | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:087. | UNOWNED |

## crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:136 | verify_finish | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. | NMO_ tx1-finish4 |
| TX1:137 | verify_observed | Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget. OPEN direct children: TX1:136. | NMP_ tx1-observed3 |

## programs/r1-cost-probe/src/lib.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:328 | first_decoded | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:094. | UNOWNED |
| TX1:330 | process_r1_cost_probe_instruction | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:333. | UNOWNED |
| TX2:213 | process_r1_cost_probe_instruction | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:221. | UNOWNED |

## programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:333 | process | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:344. | UNOWNED |
| TX2:217 | decode_lane_from_pool_release | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. | NMM_ tx2-adapters5;217/234 then233 |
| TX2:221 | process | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:240. | UNOWNED |

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Member | Remaining obligation | Owner |
|---|---|---|---|
| TX1:344 | stage1 | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:345. | UNOWNED |
| TX1:345 | stage1_owned | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX1:328. | UNOWNED |
| TX2:233 | authenticate_asq8_accounts | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:217, TX2:234. | NMM_ tx2-adapters5;217/234 then233 |
| TX2:234 | authenticate_invariant_release_registry | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. | NMM_ tx2-adapters5;217/234 then233 |
| TX2:240 | stage2 | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:241. | UNOWNED |
| TX2:241 | stage2_owned | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:242. | UNOWNED |
| TX2:242 | validate_asq8 | Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it. OPEN direct children: TX2:233. | UNOWNED |

Pool.prefix_to_cpi, NIB-P1/P2/P3/P4 and POOL.read_to_settlement retain their PCE statuses; exact member/status tables are in NMQ_PHYSICAL.md. All3 ON guard owners and3 OFF review owners remain OPEN. Latest available Pool ledger PCE15 CLOSED helpers are read-only context, no Pool promotion. Later Stream C packet claims are not silently inserted into that ledger. K086 reachability/exclusion, owner(aj)(a), L187 cold release replay/L188 artifact/extraction association and NKT-F2/F3 provenance remain; NMQ_PROVENANCE.json records the current conservative affected CLOSED rows. No remaining job-owned mathematical theorem is hidden behind Kani exhaustion; this refresh has no owned native function work and does not duplicate live owner work.
