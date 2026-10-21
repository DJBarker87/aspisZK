# Concrete V10 QueryOps builder

This packet specializes the already checked candidate query callback using the fixed `concreteOps` record. `concreteCandidateQueryOps` has no arbitrary dots/backend slot. `concrete_candidate_dots_is_literal_v10` identifies its callback with the V10 literal outer body through the checked wide-carrier maps; `concrete_candidate_query_refines_old_model` transfers a successful complete candidate query result to the old P6 callback with the same output.

The result is a Lean model/refinement composition over the selected generated owners. It does not establish Rust Std/runtime execution equivalence or adoption of the candidate source. The source-to-generated boundary and the Aeneas Std model remain explicit.

Compile receipt: Lean 4.32, `-j1 -M 4400`, exit 0, 14.273 s wall, aggregate peak RSS 3,920,199,680 bytes, `/usr/bin/time -l` peak RSS 3,919,757,312 bytes, swap 0. Launch Git revision: `2498c28ccf7a8c3ec901179fd4667a94f588a7bf`. Axiom output for both exported theorems is `[propext, Classical.choice, Quot.sound]`. The `.olean` is intentionally not included; its SHA256 is in the receipt.

The first compile attempt and the namespace/syntax diagnostic are retained under `lean-candidates/s4-v10-concrete-queryops-builder-v1-20261021/diagnostics/`.

## Source callsite link

`source-evidence/check_query_callsite.py` verifies the exact retained `query_values` source hash and first-four-statement byte span, including the call `crate::fast_dots::four_dots(q, g)`. The V10 endpoint packet separately checks candidate `four_dots`/helper bodies against the selected fixed-call body and emitted sequential four-call body. The Lean builder specializes the `QueryOps.dots` callback to that checked literal V10 endpoint. These are composed source/model links; the selected generated callback/runtime interpretation remains the explicit boundary.
