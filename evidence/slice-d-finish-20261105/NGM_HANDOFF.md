# NGM TX2 acceptance tail — active handoff

Branch codex/cx-slice-d-finish-20261105. Scope: finish_query_dot (TX2:114), finish_relation (TX2:115), finish_relation_round (TX2:116), and their still-open post-loop dependencies. tx2_common/tx2_authenticated remain NFW boundaries. No closure claimed at initialization. Target not yet established.

Budget: 100 Kani, 70 Lean, 3 extraction. One own capped scope at a time; reservation exit 0 AND allowed:true required. Host workspace/cache are prefix-owned. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; source base recorded in NGM_INPUTS.json. Shipped source unchanged. Standard axioms only. No key or wallet action.

Incoming caller: NFS TX2 query-loop certificate starts at 10, ends at 22 with fuel 12, preserving errors. It does not by itself establish the post-loop BatchedWeights write-back and reconstructed accumulator domain. Import committed NGC results read-only where applicable.

Next: inspect exact callee graph and canonical model definitions, then focused bottom-up bridges; replay closures beside NGJ_VERIFIER_IMPORT and the deployed headline. No partial certificate is a CLOSED row.
