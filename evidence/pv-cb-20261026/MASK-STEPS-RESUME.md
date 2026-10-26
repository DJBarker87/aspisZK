# op117 / V217 progress in this resume

Status: PARTIAL(candidate); no new row discharge or endpoint premise removal.

- The whole captured-source mirror check timed out at 180 seconds (`kani-step-mirror-002`). It was not rerun unchanged. This is not a counterexample.
- Exact shipped loop snippets are captured without body changes in a cfg(kani)-only proof crate. Source and snippet hashes: `mask-step-source-check.json`.
- Bounded native checks against the owned safe reference passed: c1 cell (`kani-step-c1-004`), mask cell (`kani-step-mask-005`), linear cell (`kani-step-linear-006`). No stubs; raw words unrestricted; loop bounds and sufficiency in `mask-step-kani-bounds.json`.
- Lean finite-step congruence and in-range array-cell equality: receipts 24035,24036. Specialized fill steps and full fill induction: 24037,24038.
- Prepared root equality `R1Z.PV_CB_MaskRootEq.reference`: 24041, standard axioms. Failed proof-development receipts 24039,24040 retained. This theorem compares the extracted owned control with prepared current-field control; it does not establish the fresh shipped-source binding.

Still required: remaining arithmetic/native steps, exact association of shipped control and freshly extracted reference, and the final source equation. Pure op117 has no native-composition/effect deferral.

The generic-index Horner harness timed out (`kani-step-horner-007`,180s). No counterexample was returned; any replacement must isolate coefficient selection or arithmetic before retry.

Tower step passed (`kani-step-tower-008`); prepared selection receipt24042. Linears gate009 admission refused, zero charged; next launch waits three minutes.
