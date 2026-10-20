# Generated powers array interface to checked claim powers

PROVED: generated_step_projects removes only the Usize cursor from a successful exact FnMut/back-state step, using the checked source callback's index independence. generated_trace_projects transports every ordered callback trace to the retained powers trace. generated_array_success_claim_powers then derives equality of raw returned arrays with the existing claim-powers implementation. Generic operation law is explicit in these reusable lemmas.

PROVED: sourcePowerCallback instantiates the exact source call_mut/back-state operation, and sourceArrayPowers_success_claim removes the operation-law, trace and raw-output equality premises. Every successful source powers array-interface result on canonical input equals the existing checked claim-powers result. The FnOnce field is required by the interface but is never used by from_fn_model; it is a projection of the same checked operation.

PROVED: prepared_claim_sourceArray_success transports every successful complete claim-caller output using this generated array-interface powers operation to the retained concrete caller. No array equality assumption, successful internal callback assumption or library totality premise is required. This direction suffices to reuse soundness on successful acceptance; it does not assert equality of all failed or divergent executions.

OPEN: reviewed P6 Rust standard-library correspondence, actual enclosing extracted caller installation, remaining operation/canonicality/source/runtime/artifact obligations and global 100-bit theorem. No production Rust, CU or deployment changes. These are checked typed models/bridges, not unconditional proofs of Rust Std or completed implementation soundness.

Focused NUC Lean4.32 -j1 -M4400: exit0,2.207s,371978240B cgroup peak,swap0,High1GiB/Max2GiB. All five exported theorem audits contain only standard axioms. A preceding caller extension used a nonexistent qualified core Result name; that failed diagnostic is retained. Earlier subsets passed; they were not replayed unchanged. Exact source/compiler/import/command/resource pins retained, no binaries or package replay.
