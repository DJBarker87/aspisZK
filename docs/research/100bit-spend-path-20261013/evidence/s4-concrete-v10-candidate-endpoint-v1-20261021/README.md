# S4 concrete V10 candidate endpoint

This packet freezes the checked Lean consumer `concrete_literal_outer_total_and_field_results_from_scan` with all eleven operation slots fixed to `S4ConcreteKernelOpsRootV1.concreteOps`. From scanner success, canonical gamma, successful ClaimPowers, proof/query bounds, the exact query slice, and the explicit `mapWideArray input = claimArrayToFast claimPowers` caller bridge, it derives success of the complete literal V10 four-call outer helper, equality to the fixed-helper result, mapped output equality, canonical outputs, and four field-result witnesses.

The V10 implementation is a candidate source cut. The pinned source/body checker establishes that candidate Rust entry/helper bodies match accepted V6 fixed-call Rust bodies modulo the public function name and that the pinned emitted V6 executable body has four sequential helper calls and an `Array.make` result. The separate extraction checker validates exact V10 Charon/Aeneas output receipts and hashes. Neither check proves adoption into frozen production Rust or equivalence to Rust `core::array::from_fn`; the conclusion names the checked V10 literal model.

The explicit caller-array identity remains a premise and is owned by the separate query/caller composition. Scanner success and ClaimPowers success are upstream contracts. This packet does not establish the global S4/S10 join, SBF artifact refinement, or frozen production source adoption.

The failed v1 Lean attempt is retained under `diagnostics/rejected-v1/`; it used a namespaced `mapArray` reference that did not elaborate. Only v2 is accepted. No `.olean` or other compiled binary is included.
