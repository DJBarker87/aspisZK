# Explicit low-weight candidate overlay

This is an isolated candidate-only source copy. It changes only
`input/src/statement/state_only_poseidon.rs`: the projected evaluator's
`full_low` and `internal_low` folds are expanded into ordered `QM31::ZERO.add`
operations, preserving the zero seed and exact iteration order. The independent
reference evaluator and the remainder of the projected evaluator are unchanged.

The sealed 20261016 candidate remains unchanged. `source-map.diff` and
`source-map.json` pin the before/after source file. Candidate manifest SHA-256:
`53aa43be26295c2adaec98aea5e64725344c0bfb3427d1fd6ca52d6916344e5d`.
The copied prepared runner has a new source pin and unique target/unit names;
runner SHA-256: `4f748c7310f09e7bbbad866ab7e53786bea77fed22a6b4fc4e4b023bfa78af06`.
It uses a separate `MemoryHigh=4G`, `MemoryMax=4608M`, `MemorySwapMax=0` scope.
The runner requires the pinned Linux extraction host. The first packaged-input
test attempt failed at compile setup because that extraction-only copy lacks
workspace dev-dependencies and fixture files (exit 101; no OOM). The native
workspace copy is now isolated at `/tmp/aspis-poseidon-explicit-low-folds-native-20261017`;
only its `state_only_poseidon.rs` differs from the base (base SHA
`4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe`, patched SHA
`900c1ac840dcb86560ff26736fe63e4d35a8feafe0f365278a56f472d8f3273b`). The native
test runner is `run_native_projected_tests.py` (SHA-256
`fe04751362bffa7b35b84586cd2a7de18c8c5318375b2f1e87e5f79ed8d3f3ca`); it runs
both release differential tests serially under the 4G/4608M/0-swap resource
policy and reuses the existing native Cargo target cache.

Focused optimized Rust tests for the projected evaluator are:

- `factorized_projected_oracle_matches_reference_at_extreme_field_values`
- `optimized_oracle_matches_independent_reference_at_random_off_domain_points`

Run each with `cargo test --release --lib <test-name>` in `input/`, under the
same capped Linux scope. No release or deployment claim is made by this overlay.
