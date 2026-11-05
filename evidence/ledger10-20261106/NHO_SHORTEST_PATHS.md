# Recomputed shortest entry-to-accept dependency paths

These are shortest dependency paths in the immutable599-row canonical call graph, not an execution CFG. TX1 sink is its checkpoint-producing candidate; TX2 sink is the acceptance-relation checker. All reached sibling callees and caller domains must also compose.

## TX1

| Row | Status | Function | Owner and last recorded obligation |
|---|---|---|---|
| TX1:330 | OPEN | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | NHD_: Full original AccountInfo/data forwarding, route domain, child process certificate and model/native/effects composition. |
| TX1:333 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | NHD_: Admitted route eliminates lifecycle branches; exact stage1/stage2 arguments and all returned Results/effects; both child packets. |
| TX1:344 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 | NHD_: All three snapshot packets, SDK mutable borrow, SAME checkpoint bytes, KMX one-window copy/frame and cleanup. |
| TX1:345 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned | NHD_: All account guards/data/canonical decode domains and proof-prefix validation, first_decoded, exact result/cleanup order. |
| TX1:328 | OPEN | programs/r1-cost-probe/src/lib.rs::first_decoded | NHD_: SAME public/proof/split and deployed None observer; candidate tx1 packet plus error mapping/logging and full result/cleanup. |
| TX1:094 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx1 | NHL_ prepare/tx1 model lane; NFW_ retained native producer boundary: Candidate tx1 composed packet and exact public/proof/S2/split/prepared/query/checkpoint domains needed by first_decoded. |

OPEN sequence: TX1:330, TX1:333, TX1:344, TX1:345, TX1:328, TX1:094.

## TX2

| Row | Status | Function | Owner and last recorded obligation |
|---|---|---|---|
| TX2:213 | OPEN | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | NHD_: Full original AccountInfo/data forwarding, ASQ8 route domain and child process certificate. |
| TX2:221 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | NHD_: ASQ8 first-byte disjointness, same input stage2 forwarding and exact Result/effects. |
| TX2:240 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 | NHD_: Empty return-data clear, seven snapshot packets, clock syscall exact reply and stage2_owned forwarding/cleanup. |
| TX2:241 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned | NHD_: Full validate_asq8 authentication/data/statement provenance, SAME tx2 inputs, error callback and emit_result composition. |
| TX2:064 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated | NHL_ prepare/tx1 model lane; NFW_ retained native producer boundary: Authenticated candidate packet; public/proof/checkpoint exact domains passed by stage2_owned. |
| TX2:065 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common | NHL_ prepare/tx1 model lane; NFW_ retained native producer boundary: Common TX2 packet and all prepared/resume/query domains with None observer. |
| TX2:115 | OPEN | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation | NHE_/NHI_ TX2 tail; parent finish_relation remains OPEN: NGW point/weight constructors, NHE polynomial/round/dot and NHI scalar_factor/tensor are CLOSED. Remaining pair TX2:129, filled/factored/grouped/process_kind/byte/high/shared/partial wrappers and SAME Prepared/view producer boundaries must compose, with full errors and frames. |

OPEN sequence: TX2:213, TX2:221, TX2:240, TX2:241, TX2:064, TX2:065, TX2:115.

## Adjacent blockers and provenance

NHD_SPINE.md supersedes the NGL ownership report for entry/adapter rows. Ruling(ak) provides explicit-constructor logging stubs for non-Arbitrary Result interfaces; it supplies no callee packet by itself. NHF closes only wide_view TX1:095; prepare TX1:087 and Prepared::new TX1:179 remain OPEN. The pinned NHL branch snapshot provides model advances only, zero composed row promotions. TX1:137 verify_observed remains OPEN, despite the11 NGX leaf packets (two already CLOSED in NGZ).

NHE/NHI replace obsolete scalar_factor/tensor blockers with their CLOSED packets; pair TX2:129 and finish_relation TX2:115 stay OPEN. Full remaining member table: NHI_PAIR_CONE.md. Pool production prefix/settlement ownership is NHC_, outside599; supported_loader is CLOSED while AccountInfo/decoder/marker/custody/registry/CPI/same-return association remains OPEN. NHC_POOL_B.md and NHC_REMAINING.md supersede the old NGG item10 conflict: canonical retarget is complete, production native associations remain.

Every OPEN spine row above has an explicit owner and last recorded obligation. A currently running worker is not evidence of closure. No live sibling worktree was read or edited. See NHO_READONLY_PROVENANCE.json for immutable sibling revision.
