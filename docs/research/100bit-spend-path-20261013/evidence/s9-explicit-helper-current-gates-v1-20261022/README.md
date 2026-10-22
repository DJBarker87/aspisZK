# S9 explicit-helper current-source gates

This packet records native, SBF, six-fixture CU, output-equivalence, and strict-stack results for the isolated S9 `factored_s2_libra_weights` candidate. It is evidence for review only; no research production files were changed by this gate run, and no adoption or deployment is claimed.

The tested source was research HEAD `7998f6355d7163b5df1550f3440041b5b79dd48b` plus the candidate `weights.rs` at SHA-256 `9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`. The already-reviewed S4 source blobs are at HEAD. The run’s complete 60-file Rust/Cargo manifest is retained at `receipts/work/src/s9-candidate-source-manifest.json` and the candidate’s source hashes at `receipts/source-pins/current-candidate-rust-cargo.json`.

The candidate SBF artifact is retained only on the build host at `/home/dombarker/project-offloads/s9-explicit-helper-v1-20261022/attempt3/artifacts/aspis_r1_cost_probe_program.so`, SHA-256 `5aac14ef69f482c8b3bc95a400c321288b6a27f2b5b96adabcd21ad0c41019eb`. No ELF, shared object, keypair, or proof binary is included in this packet. Fixture inputs are identified by hashes in the per-fixture command records.

Admission used a fresh global cgroup inventory: finite reservations 24.375 GiB, uncapped charged usage about 8.90 GiB, and all three admission predicates passed. Each stage ran in its own cgroup with `MemoryHigh=10 GiB`, `MemoryMax=12 GiB`, `MemorySwapMax=0`; per-process/scope timing and memory receipts are retained. Native optimized tests exited 0 in 5.306 s (process peak RSS 210,976 KiB, scope peak 505,712,640 B). SBF compile/link exited 0 in 6.106 s (process peak RSS 201,500 KiB, scope peak 437,571,584 B). The six verifier fixtures and strict stack audit also exited 0; fixture commands each completed in about 0.114 s, with zero swap and no cgroup memory events.

Each fixture is within the separately authorized +12,000 CU ceiling on both stage 1 and settlement, and both the stage-1 checkpoint-tail digest and return-data digest match the frozen baseline. The six exact measurements are in `receipts/gates/gate-result.json`. Legacy strict B1 fails for all six, and the older runner’s settlement +10,000 comparison also fails for all six; those outcomes are retained and are not waived by the +12,000 comparison.

The strict stack audit used the linked ELF SHA-256 `d7dd4d3b164cc0930c49c0b53fe5566f164713ed2aed40bee80c7692f9c8d9ab`, the candidate stripped artifact hash above, and build-log SHA-256 `9e0f20b7355a7e1c586ddcd38ad6bee97c89f59dd22cc6e1122b3b7d7bfe175e`. Its receipt reports exit 0 and no surviving stack diagnostics. Binary inputs remain on the build host.

Run `python3 check.py` from this packet to verify the retained source, baseline, artifact metadata, cgroup limits, six fixture outcomes, output identity, and absence of binary payloads.
