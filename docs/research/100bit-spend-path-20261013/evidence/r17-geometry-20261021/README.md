# R17 geometry receipts

Read `../../design/R17-GEOMETRY-20261021.md` for the status and exact scope.

- `accepted-summary.json`: two accepted focused Lean modules, 14 full theorem audits.
- `manifest.json`: all four closed-form attempts plus the boundary attempt, including errors.
- `rust/receipt-1.json`, `output-1.log`, `time-1.log`: optimized executable certificate, all three tests pass.
- `rust/remote-input-comparison.json`: all 93 copied dependency hashes match local pins.
- `table-bytes.json`: sizes, canonical byte encoding and table hashes.
- `generator-check/`: `generate_fast_domain.py --check`, exit 0.
- `remaining.tsv`: exact table and source-execution residuals.

No premise deletion is claimed. The successful Lean source snapshots are
retained beside their receipts; failed drafts are identified by SHA and full
compiler diagnostics. Failed error-recovery axiom output is not accepted.
The containing commits pin the new sources; each receipt pins the HEAD and
working source hash at invocation time. No fresh release manifest is claimed.

To reproduce the Rust certificate, copy the pinned core, root workspace
metadata, the two included source files and `tools/r17-geometry-20261021/`
to a dedicated build workspace. Run `cargo test --release -j 4 --manifest-path
tools/r17-geometry-20261021/Cargo.toml -- --nocapture --test-threads=1` inside
`systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G
-p MemorySwapMax=0 -p TasksMax=64`, after checking the populated reservation
stays below the host limit. The original scope ran concurrently with 8G and
7G scopes (23G total including this 8G scope, below the 55G safe limit).
The host wrapper is a record of that attempt, not permission to overwrite
or repeat an unchanged receipt.

Lean reproduction uses `run-lean.py ModuleName` with the recorded retained
cache paths available. It refuses a receipted unchanged source, uses a private
object directory and the shared mkdir lock, and never rebuilds dependencies.
