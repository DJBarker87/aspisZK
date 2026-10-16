This is a source-only native differential kit for Decision 1c. Baseline is `3335eecf2f2a08096abe95c67ac6b304f2df6284`; final production source is `96aad8ef209cb69d7667ab5d8728bd4584a86d16` (same verifier source as C's `e5c186ba3`). No production source is edited by generation. No test has been run by the kit author; A owns capped optimized execution and receipts.

`prepare.py --check` verifies generated exact-body modules and source pins. `--stage PATH` writes only an isolated source snapshot. It rejects the repository itself. The actual fixture overlay adds two cfg(test,prover,private-leaf-salts) entry hooks (geometry and query), appends the whole baseline tx1 under `migration_old_tx1`, and symmetrically wraps checkpointing as a fallible test call. Source slices include the full function signatures/bodies from their first declaration line through the matching brace; surrounding attributes are not part of these body hashes. All transformations are listed in `source-pins.json`.

The checkpoint adapter injects `Err(Error::Checkpoint)` immediately before the actual infallible checkpoint function and its three hashes; this is not a production-reachable error. On success it calls the actual checkpoint function. The new production tail's non-test branch retains its original checkpoint expression. Geometry/query failures return `Error::Query` at the entry of the actual respective routine. Query 0 fails before its Merkle/observer effects; query 21 fails after queries 0..20. These configured interface failures are synthetic, including in the real fixture gate.

To compose with A's Prepared overlay, first stage that overlay on the final source. Then run locally (Git refs are required):

```sh
python3 -B tools/r1-tx1-migration-kit/prepare.py --check --stage ISOLATED_SOURCE --base-overlay-pins /path/to/r1-prepared-migration-kit/source-pins.json
```

The existing verifier must match the explicit prior overlay hash and retain final production bytes as its prefix; it is not silently overwritten. The output `tx1-migration-overlay.json` pins the exact composed files and prior overlay manifest. Copy these two changed source files and that manifest into A's injected snapshot. Keep clean final source for codec/counter/checkpoint gates. Include both overlay manifests in the injection evidence. The standalone kit also needs its Cargo files, harness and generated `shared/` modules staged under `tools/`.

The real saved S2 layer uses the existing transfer-1023 P3 proof and ASF8 public input pinned in `source-pins.json`. It retains actual SHA, field arithmetic, parsing, semantic verification, preparation, query bodies, accumulator and checkpoint. It compares complete outcomes, all observer callbacks (including enabled detail phases), actual `trace::value` sequences, digest slice boundaries/answers, boundary calls and complete Prepared/Accumulator snapshots. Failure observations must be prefixes of the successful execution. Geometry fails just after Prepare; first query has that same observer cut; last query fails before Merkle(21); checkpoint fails before CheckpointWrite. Success must reach all 22 query calls and finish with CheckpointWrite. A should run:

```sh
cargo test --verbose --release --locked --offline -j1 -p aspis-r1-cost-probe --features prover,private-leaf-salts,optimized-terminal,detail-phases --lib verifier::tx1_migration_tests::tx1_saved_s2_exact_old_new_faults_and_success -- --nocapture --test-threads=1
```

This produces five cases: four synthetic interface failures and one actual saved-fixture success. The detail-phases feature is explicit; the output records its enabled state. Default and detailed observer sequences are not silently equated.

The separate shared-interface layer includes the exact whole baseline tx1 and final tx1+tx1_finish in different modules, with only the same checkpoint Result-call transformation. Its E is `u64`, parsing/semantic verification/preparation/geometry/query/checkpoint are common synthetic interfaces, and its recorded digest is a deterministic byte recurrence, **not SHA or the production sampler**. It proves no field equivalence, authentic opening or production acceptance claim. It checks Rust call order, Result propagation, state/trace prefixes, marks and observer callbacks for S1/S2/D in both explicitly selected default and detailed observer modes. It produces 30 cases (24 injected failures, six success controls). Run it separately:

```sh
cargo test --verbose --release --locked --offline -j1 --manifest-path tools/r1-tx1-migration-kit/Cargo.toml --lib -- --nocapture --test-threads=1
```

Expected final markers are `TX1_REAL_S2_PASS cases=5` and `TX1_SHARED_PASS cases=30`. Retain every per-case output and both complete logs. Run only in A's allocated host scopes with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, aggregate reservations below the safe host limit, and one job per declared native scope. Use the fixed artifact scanner/runner and preserve successful child exit/time/RSS/swap independently if wrapper postprocessing fails. No proof generation, Lean, SBF rebuild or runtime harness is part of this kit.
