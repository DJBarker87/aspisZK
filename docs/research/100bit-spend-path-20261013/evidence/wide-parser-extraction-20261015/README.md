# WideExact parser extraction preflight

These isolated attempts exercise only the actual `WideExact::from_le_bytes` parser through `crate::parse_wide_exact_probe`. They use complete pinned field sources from worktree revision `aba310f1daa065a27da89d15c6c47166037a8a71`. The repository runtime sources were not edited. Every attempt used the same pinned Charon/Aeneas pair, `--mir built`, `core::option` and `core::result` includes, release/offline Cargo settings, and a `MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128` scope. `--monomorphize` was used in a/b and omitted in c/d to match the prior successful field parser run.

The baseline `WideExact::from_le_bytes` source was tested in a and c. The candidate in b and d changes only that function body to check the 32-byte length and parse two 16-byte `QM31` slices, returning `Some(Self { c0, c1 })`; `from_limbs` is untouched. The exact diff and source pins are retained.

- a: Charon succeeded; Aeneas failed with “Nested-loop returns require exactly one Option language item” at `wide_exact.rs:254–261`, Aeneas `PrePasses.ml:918`.
- b: Charon succeeded; Aeneas failed during type-name registration because `core.option.Option<WideExact>` and `core.option.Option<Infallible>` collide, Aeneas `ExtractBase.ml:269`.
- c: Charon succeeded; Aeneas failed with “Markers remain after collapsing a context,” ended regions `{11, 14}`, while processing the baseline loop implementation.
- d: Charon and Aeneas both succeeded. Translation output includes `WideExact`, `WideExact.from_le_bytes`, the probe wrapper, M31/CM31/QM31 declarations and parsers, and the two non-local Option helper bodies. The type and body reuse comparison is in `generated-field-reuse.md`.

The preserved a wrapper result file incorrectly reports exit 0 because its `if ! command; then status=$?` logic captures the inverted status. Its authoritative `commands.json` and `translate.time.log` record Aeneas exit 2; `attempt-a-status/corrected-stage-status.json` explains this without changing the raw run. b/c/d wrapper status files record their actual exit values.

Attempt archives exclude only Cargo `target/` caches. They retain source copies, LLBC, generated files when available, command/environment/tool pins, stdout/stderr logs, and per-stage GNU time logs. The successful generated Lean files were not compiled. These extraction results do not establish Rust compiler correspondence or validate callers.
