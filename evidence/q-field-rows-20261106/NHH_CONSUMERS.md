# NHH source-boundary consumers

The following reachability is from the unchanged NGZ conservative graph. It identifies potential driver cones, not actual call instances or driver closure. Typed alternatives remain explicit in NHH_SOURCE_GRAPH_FINDING.md and NHH_EDGES.json.

## crates/aspis-core/src/r0/scalar.rs::M31::from_m31

Rows: TX1:NGB008, TX2:NGB012. Domain: every raw u32 input, no canonicality or successful-return premise.

Immediate conservative consumers: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::CM31::from_m31

Rows: TX1:NGB007, TX2:NGB010. Domain: every raw u32 input, no canonicality or successful-return premise.

Immediate conservative consumers: crates/aspis-core/src/r0/scalar.rs::QM31::from_m31.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::QM31::from_m31

Rows: TX1:NGB005, TX2:NGB009. Domain: every raw u32 input, no canonicality or successful-return premise.

Immediate conservative consumers: crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31

Rows: TX2:046, TX1:NGB003. Domain: every raw u32 input, no canonicality or successful-return premise.

Immediate conservative consumers: crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/field.rs::CM31::from_m31

Rows: TX2:NGB011. Domain: every raw u32 input, no canonicality or successful-return premise.

Immediate conservative consumers: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/field.rs::CM31::inv

Rows: TX1:005. Domain: SAME canonical two-word receiver; exact zero assertionFailure and nonzero returned record.

Immediate conservative consumers: crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/field.rs::QM31::try_inv

Rows: TX1:034. Domain: SAME canonical four-word receiver, including zero.

Immediate conservative consumers: crates/aspis-core/src/circle.rs::secure_circle_point_from_parameter; crates/aspis-core/src/field.rs::QM31::inv.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/field.rs::QM31::inv

Rows: TX1:027. Domain: SAME canonical four-word receiver; exact zero panic and nonzero returned record.

Immediate conservative consumers: crates/aspis-core/src/field.rs::QM31::try_inv; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range.

Potential driver cones: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

Actual source CM31 inverse is consumed by QM31::try_inv on its SAME canonical nonzero quartic norm; the new Q packet proves that domain, rather than assuming it. The inverse wrapper consumes the SAME derived Some child reply. Circle::secure_circle_point_from_parameter is the real try-inverse parent and must supply canonical parameter/domain and its original source/cohort carrier; this job closes no circle/Prepared/entry driver row. The newly closed embeddings supply unrestricted raw-word source laws plus the SAME canonical accumulation callback association.

The default inv_with(M31::inv) edge is a fixed specialized callee packet; generic TX1:006 remains OPEN. QM31 negation has no adopted endpoint association and unblocks no certified driver edge yet.
