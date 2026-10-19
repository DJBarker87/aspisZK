# Candidate 12: complete reference coefficient traversal

Candidate 12 remains open. This checkpoint connects the full emitted reference coefficient loop to the checked optimized arithmetic batch; it does not equate the optimized source loop to that batch.

`CuSavingsRhoReferenceTraversal.source_eq` names the entire emitted `AspisR1RhoCoefficients.rho_old.coefficients` function. Under the source caller bounds (next <= 22 and weights length <= 256), it equals the previously checked finite reference updates. It does not assume canonical input weights, successful callbacks, termination of an arbitrary callback or an admitted abstract index list. Arithmetic failure and divergence are preserved. The source Range iterator's actual checked increment supplies the finite traversal; `CuSavingsRhoRangeInputs.pairs_eq` identifies its list with the rho items, giving unique full coverage.

Both diagnostic arguments still execute. The exact constructor dependency slice, including all four concrete CodeField.from_m31 implementations, was extracted from the candidate's unchanged source. The generated diagnostic bodies are unchanged; identical field carriers and modulus are reused. `CuSavingsRhoDiagnostics` proves both constructors total even on raw noncanonical words. The non-prover trace function is the exact emitted no-op. `trace_index_steps` proves the two executed index calculations cannot overflow under the caller bounds. No diagnostic argument evaluation was silently dropped. The extraction kit's unresolved from_m31 call is bound to the concrete emitted CodeField method, not to its unreachable stub.

`CuSavingsRhoSourceBatch.source_batch` consumes the complete reference source function and the actual emitted common basis result. It derives index/basis admission and compares the reference source output with the canonical projection of the optimized arithmetic batch, preserving its Good invariant and single counter increment. The canonical power, Good/count invariant and caller next/length bounds remain explicit until their enclosing source callers are connected.

The projected-field source slice still requires enclosing accumulate composition: stable power/next reads and the unique mutable weights projection are inverse-substitution checked, not claimed as an automatically emitted whole accumulator proof. The optimized source Option reborrow interface is still unresolved; no template axiom or speculative replacement handback is imported. Sufficient-resource reservation/SDK binding and tx1_finish/tx2/tx2_authenticated checkpoint/cryptographic/effect composition also remain open.

Run `python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-rho-reference-traversal.py` for exact source, promotion, coherent cache, dependency object and axioms audits. The JSON enumerates every accepted target, command, source revision, features, exit, wall time, RSS and swap. The consuming theorem and all accepted new results use only propext, Classical.choice and Quot.sound. Failed local attempts are retained as failures, not release evidence. No unchanged Lean full regression or CU/runtime suite was rerun.

Production Rust is unchanged. New extracted declarations used by this proof are listed below; no production function was changed in this checkpoint.

| Source function | Source-bound Lean declarations |
|---|---|
| Old accumulate coefficient for-loop, after explicit stable-field projections | AspisR1RhoCoefficients.rho_old.coefficients_loop.body; rho_old.coefficients_loop; rho_old.coefficients |
| canonical_qm31 and WideExact::from_qm31 | AspisR1CuRho.field.canonical_qm31; field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call; field.WideExact.from_qm31 |
| Four concrete CodeField::from_m31 methods | AspisR1CuRho.field.{M31,CM31,QM31,WideExact}.Insts.Aspis_r1_rho_diagnosticsScalarCodeField.from_m31; AspisR1CuRho.from_m31 wrapper |
| CM31::from_m31, QM31::from_cm31 | AspisR1CuRho.field.CM31.from_m31; field.QM31.from_cm31 |
| Non-prover trace::value | AspisR1CuRho.trace.value |
