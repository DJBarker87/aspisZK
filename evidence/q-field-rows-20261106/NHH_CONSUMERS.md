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

## CM31::inv — TX1:005

The actual frozen QM31::try_inv computes a CM31 norm and calls this inverse on that SAME norm. NormInverse.quartic_norm_nonzero plus NHH_CMAlgebra square/rotate/sub laws establish its canonical live domain. The conservative inventory instead lists a QM31 inverse alternative at that site; no authoritative edge repair is booked here. The inverse packet can be used by the QM31 try-inverse driver boundary once the complete caller log/association is audited. The inventory's QueryGeometry::for_range alternatives are recorded separately; its actual scalar inversions do not become CM31 calls.

Its only conservative incoming route reaches the Q geometry roots; reverse conservative reachability also reaches the driver entry/prepare/finish cones. Closure supplies a local callee packet on the explicit domain and does not close those drivers. Generic inv_with remains an open row even though the fixed inv_with(M31::inv) callee instance composes at CM31::inv.
