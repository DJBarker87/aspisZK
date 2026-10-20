# Frozen encoding uniqueness regressions

See `../../design/ENCODING-UNIQUENESS-20261021.md` for scope, results and limits.
All new Rust code is in `cfg(test)` inside this tools-only standalone crate.
No shipped program or crate source is changed.

Native command (on the build host, in a fresh 6G/8G/no-swap/64-task scope):

```
cargo test --manifest-path tools/encoding-uniqueness/Cargo.toml --release --offline --locked -j 4 -- --nocapture
```

`run-frozen-host.py` records the source overlay and exact capped launch used
for the final evidence. It reads the earlier identity-checked ASQ8 host source
workspace and writes only this task's private host directory. It intentionally
refuses to overwrite snapshots/receipts. The local worktree keeps the research
base sources; only the private host copy was overlaid for frozen verification.

`evidence/source-inputs.json` is the initial task-base upload manifest for the
six-test preflight. `frozen-run-inputs.json` is authoritative for the seven-test
frozen run. `frozen-source-comparison.json` records all inherited differences.
All compiler output is retained under evidence/receipts. No binary or key is
committed. Host target/cache remains private; no local target directory exists.
