# R345: exact ControlFlow source translation limits

The reviewed R334/R339 projections retain the original selected source rows and their typed dependencies, without altering bodies, signatures, types, regions or language items. R338 translation of all three methods exited 2 in 0.18 seconds (54,032 KiB RSS, zero swaps): the translator refused a variant-field expansion in from_residual. R343 translation of from_output alone exited 2 in 0.21 seconds (55,440 KiB RSS, zero swaps): the target naming step gave two concrete ControlFlow types the same Lean name. Neither emitted Lean output.

[Complete reviewed evidence](evidence/r345-controlflow-source-frontier/lead-review.json) preserves exact inputs, source/tool/runner hashes, revisions, resource receipts, full failure logs, decoded source inventories, and earlier incomplete projection history. These are source/tool diagnostics; there is no axiom report or formal execution theorem.

First remaining proposition: faithful source traversal and closure execution, after resolving empty-type handling and target-name collisions without changing original source operations or constraints. Original guards, fold/extend, complete callback chronology, universal joint privacy and soundness remain open. Verifier source, all security parameters and 999,790 / 999,532 CU are preserved; no benchmarks or unchanged regression suites reran.
