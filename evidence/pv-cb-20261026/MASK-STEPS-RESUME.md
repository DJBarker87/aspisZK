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

Prepared replacement for timed-out Horner: separate arbitrary-index coefficient selection (`horner_index`) from the arithmetic on a uniform coefficient array (`horner_uniform`). The latter alone does not quantify over arbitrary coefficient arrays; a locality/source theorem is required to compose them. No universal Horner pass is claimed from these restricted gates.

The full linear helper passed (`kani-step-linears-010`,110.62s,700832KiB,swap0). Horner cell locality is proved in Lean (`PV_CB_HornerCell`,24044); prepared reverse-body congruence is proved in24046 (failed development24045 retained). These are semantic ingredients, not a fresh source binding.

Power-chain native gate011 timed out180s. Index-only Horner replacement012 passed. Fresh Charon root extraction passed (`charon-source-op117-fresh-root`); Aeneas admission was refused twice (fresh-root and fresh-root-002), both uncharged. Continue with next unused receipt name after the three-minute wait; no cap changes.

Fresh root Aeneas (`aeneas-source-op117-fresh-root-003`) fails at loop join/collapse with `Not_found`, `InterpReduceCollapse.ml:1991`. Charon succeeded first. This is the exact current-source extraction obstruction; it is unrelated to native composition. Continue the P6 reference route and preserve all passing step evidence.

The uniform-coefficient Horner arithmetic gate013 also timed out180s. This changed-property isolation did not prove the remaining arithmetic gate. Stage3 is retained as PARTIAL with exact source/P6 obstructions; proceed to the later pure operations using the remaining Lean budget. No whole-run/native-composition boundary is substituted.
