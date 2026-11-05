# NHH slice-boundary consumers

Only explicit source-graph reachability is listed. A closed field row does not close an enclosing driver.

## crates/aspis-core/src/r0/scalar.rs::M31::from_m31

Rows: TX1:NGB008, TX2:NGB012.

Immediate consumers: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31.

Driver cones reached: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31; crates/aspis-core/src/r0/scalar.rs::QM31::from_m31; crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31; crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::CM31::from_m31

Rows: TX1:NGB007, TX2:NGB010.

Immediate consumers: crates/aspis-core/src/r0/scalar.rs::QM31::from_m31.

Driver cones reached: crates/aspis-core/src/r0/scalar.rs::QM31::from_m31; crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31; crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::QM31::from_m31

Rows: TX1:NGB005, TX2:NGB009.

Immediate consumers: crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31.

Driver cones reached: crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31; crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31

Rows: TX2:046, TX1:NGB003.

Immediate consumers: crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node.

Driver cones reached: crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.

## crates/aspis-core/src/field.rs::CM31::from_m31

Rows: TX2:NGB011.

Immediate consumers: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31.

Driver cones reached: crates/aspis-core/src/r0/scalar.rs::CM31::from_m31; crates/aspis-core/src/r0/scalar.rs::QM31::from_m31; crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31; crates/aspis-r1-cost-probe/src/candidate.rs::prepare; crates/aspis-r1-cost-probe/src/candidate.rs::tx1; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new; programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction.
