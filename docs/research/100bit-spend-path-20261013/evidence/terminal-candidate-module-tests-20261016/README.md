# Candidate terminal module tests

This bundle records an optimized Rust unit-test run against the isolated terminal Copy-helper/indexed-fold candidate at base revision `a8930e677bc745854b9f693b5628c8a8bd2ac848`. It does not change production sources and makes no settlement or universal equivalence claim.

The candidate overlay pins the three source files in `source-snapshot/candidate/`: `lib.rs` (`fd7a32a1dd9755925f318388f5895d2cd129c6697aa5969a403014e86249353b`), `state_only_poseidon.rs` (`4324116f9e652d31190037ab7c5205f3107991143e4a2bbca701346b0bba66ba`), and `pool_v1/pair_forest_semantic_terminal.rs` (`41da553efb32cc342a7002ecdee8ba1909e1531dfa2b6facc95983495135c7cc`). The full 508-path source input manifest is included; the full copied candidate workspace and SBF evidence are in the sibling `terminal-copy-indexed-replay-20261016` bundle.

Attempt a failed in the runner's Rust toolchain preflight before Cargo started: the runner's environment omitted the cargo-bin directory from `PATH`, so `rustc -Vv` was not found. Attempt b corrected only the runner `PATH` and used a fresh output path. In one `MemoryHigh=8 GiB`, `MemoryMax=10 GiB`, `MemorySwapMax=0`, `TasksMax=128` scope, it ran two optimized, locked, offline tests with one Cargo job:

- `state_only_poseidon::tests`: 10 passed, including random off-domain oracle/reference comparisons and extreme field-value checks; 61.03 seconds, cgroup peak 586,174,464 bytes, swap 0.
- `pool_v1::pair_forest_semantic_terminal::tests`: 6 passed, including randomized off-domain factoring, packed-range comparison, honest transfer/withdrawal Boolean rows, and occupancy/append rejection checks; 0.50 seconds, same scope peak, swap 0.

The resource preflight recorded external minimum 24 GiB + own Lean reserve 6 GiB + this Rust scope maximum 10 GiB = 40 GiB against the 50 GiB limit, with no active external compiler scopes. Compilation and focused test execution were expected; no proof generation, SBF build, or key generation occurred.

The earlier 1,233-case trace is retained in `terminal-validator-extraction-20261016`; its trace calls the pair-terminal codec/afterstate functions and does not call the functions changed by this candidate. This bundle therefore runs the current candidate's source-specific randomized/off-domain unit tests and does not relabel the older trace as candidate coverage.
