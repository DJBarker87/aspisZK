# Proposed fresh native/SBF gate plan (not launched)

Candidate source: `attempt2/candidate/src/weights.rs`, SHA-256 `9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`. Base S4 overlay receipt is `evidence/s4-current-overlay-revalidation-v1-20261022/`; its source revision is `5b23a95e6386a02fe12540403aa46067ee167c0d`, overlay hash `cf17ce6133647076fde2a413171602121e3cd793537389afdf157788f27e3ca7`. Current overlay native and SBF source trees/caches must remain unchanged. The proposed new run uses a separate immutable run2 source/artifact directory and inserts only this candidate `weights.rs` blob into the reviewed S4 three-source base. It must re-pin every admitted Rust source file and Cargo.lock before launch.

The current-overlay receipts name reusable NUC target caches:

- Native Cargo target: `/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/native-target`
- SBF verifier target: `/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/sbf-target-verifier`
- Prior source tree: `/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/src`
- Prior artifact: `/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/artifacts/aspis_r1_cost_probe_program.so`

Do not write into the prior source or artifact directory. Reuse target caches sequentially only after fresh NUC admission confirms no concurrent writer. A copied source root can change Cargo package path fingerprints, so the actual incremental rebuild scope is not guaranteed; expected work is an optimized rebuild of changed local crate(s), native test execution, and SBF program compile/link. Retained current-overlay measurements were 0.401 s and 121,720,832-byte scope peak for native tests, and 2.202 s and 145,014,784-byte scope peak for SBF build, but these were unchanged-source cache hits. They are historical estimates only, not expected candidate receipts.

After review/admission, run sequentially, each under its own fresh scope using `MemoryHigh=10GiB`, `MemoryMax=12GiB`, `MemorySwapMax=0`, `-j4`, and collect actual child/cgroup paths and source/artifact hashes:

1. Native optimized check from the run2 source root:
   `cargo test --release --offline --locked -j4 -p aspis-r1-cost-probe`
   with `CARGO_TARGET_DIR` pointing at the retained native target above and `CARGO_NET_OFFLINE=true`.
2. SBF artifact build from the run2 source root:
   `/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf --manifest-path <run2>/work/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir <run2>/artifacts --features pool-adapter,private-leaf-salts --skip-tools-install --offline -j 4 -- --locked`
   with `CARGO_TARGET_DIR` pointing at the retained SBF verifier target and offline Cargo env. Inspect final ELF identity and stack report.
3. Run the existing standing-runner-v2 six-fixture CU/settlement and stack checks against only the run2 artifact. Retain the same six fixtures and strict 1.4M runtime limit, compare stage1 and settlement independently to the exact B1 predicates, and do not apply a diagnostic compute override or waive a failure. The expected simulation phase is CPU-bound and per-fixture; do not put fixture simulations into an unscoped build phase.

The standing evidence reports previous candidate stage1 maximum `1,210,100 CU` and settlement maximum `1,189,265 CU`; those do not predict this candidate. Existing six fixture identities and outputs may be reused as inputs, but every candidate run must bind its result to the new verifier ELF SHA. Do not re-run unrelated audit/eight-way gates unless the exact source cone makes them relevant. This is a plan only; no admission request, build, fixture simulation, or source deployment has been made.
