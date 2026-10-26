# rw18 Kani allocation

20/20 charged; 16 verified, four 240-second timeouts, no checked counterexample. Harness names were listed before charging in `KANI-PLAN.json`. Timeout results are not certificates. No timed-out harness was rerun unchanged.

All runs used optimized proof-local Rust, cadical, default overflow checking and unwinding assertions. Lean supplies the arbitrary-slice iterator/context induction and the 17-step sufficiency theorem for arity16. Restricted arithmetic gates do not replace full-width source correspondence.

Kani012 `zero_lambda_16` was a restricted whole-helper diagnostic and exceeded the per-step-only instruction. It remains charged and is not used as the universal source certificate. All later gates were per-step.

|Run|Harness|Exit|Wall s|Peak RSS KiB|Swap|
|---|---|---:|---:|---:|---:|
|pv-rw18-empty-original-001|gates::empty_original|0|0.399|153836|0|
|pv-rw18-empty_combined-002|gates::empty_combined|0|1.054|161284|0|
|pv-rw18-exhausted_combined16-003|gates::exhausted_combined16|0|2.179|179700|0|
|pv-rw18-exhaustion_stable16-004r2|gates::exhaustion_stable16|0|2.267|280720|0|
|pv-rw18-next16_from_initial-005|gates::next16_from_initial|0|3.419|281640|0|
|pv-rw18-next16_from_suffix-006|gates::next16_from_suffix|0|8.762|281976|0|
|pv-rw18-next16_last-007|gates::next16_last|0|2.530|280060|0|
|pv-rw18-next16_preserves_tail-008|gates::next16_preserves_tail|0|4.178|280220|0|
|pv-rw18-next16_preserves_source-009|gates::next16_preserves_source|0|2.645|278816|0|
|pv-rw18-zero_power_state-010|gates::zero_power_state|0|0.534|143192|0|
|pv-rw18-zero_lambda_single-011r1|gates::zero_lambda_single|0|0.587|153744|0|
|pv-rw18-zero_lambda_16-012|gates::zero_lambda_16|0|6.935|283676|0|
|pv-rw18-unit_power_zero_value-013|gates::unit_power_zero_value|0|0.460|142736|0|
|pv-rw18-canonical_scalar_mul-014|gates::canonical_scalar_mul|124|240.004|16192|0|
|pv-rw18-canonical_scale_c0a-015|gates::canonical_scale_c0a|124|240.004|15664|0|
|pv-rw18-canonical_power_c0a-016|gates::canonical_power_c0a|124|240.004|16016|0|
|pv-rw18-reduce64_product_bound-017|gates::reduce64_product_bound|0|0.268|135944|0|
|pv-rw18-canonical_add_bound-018|gates::canonical_add_bound|0|0.263|136948|0|
|pv-rw18-canonical_reduce64_bound-019|gates::canonical_reduce64_bound|0|0.264|136972|0|
|pv-rw18-canonical_scalar_product_u16-020|gates::canonical_scalar_product_u16|124|240.004|16016|0|

Each run directory retains the exact target, source hashes/revision, input preflight, caps, stdout/stderr and structured receipt. Preflight refusals are retained separately and not charged. Four timeouts: canonical_scalar_mul, canonical_scale_c0a, canonical_power_c0a, canonical_scalar_product_u16.

All32 recorded native cgroups are absent. Shared anonymous solver files could not be attributed from retained PID/ownership metadata and were left intact; see host-recorded-cgroups-final.json and solver-temp-ownership.json. The requested pinned host cache is retained.
