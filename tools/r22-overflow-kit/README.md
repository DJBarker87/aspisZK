# Frozen R22 arithmetic packet

Read the status and residual table in
`docs/research/100bit-spend-path-20261013/design/R22-OVERFLOW-20261021.md`.
R22 remains open. This kit supplies conditional numeric/body-step proofs,
not whole-cone accepted-run refinement.

Install requirements in a temporary virtualenv. Read-only checks:

```
python inventory.py --check
python extend.py --check
python audit.py
```

Run from the repository root with `tools/r22-overflow-kit/` prefixes. `extend.py`
is the final generator; `prepare.py` generates only the historical base stage.
`results.py` regenerates the per-site TSV and explicitly separates proved local
bounds, primitive semantic rules, iterator boundaries, cfg exclusions and open
sites. It does not infer Rust types or resolve the deployed call graph.

`snapshot-inputs.py` binds every historical receipt to exact source files. All
snapshots are source only. The isolated Cargo crate has no dependencies and
uses opt-level3, overflow-checks=true. Arithmetic wrapping calls are instrumented
only in the tool copy; the raw-coordinate and residue-row abstractions are
explicit independent-product overapproximations, not exact function replay.

Kani runs only on the build host in the job's own directory. Each exact harness
uses its own 6G/8G/no-swap/64-task scope. The launcher checks aggregate populated
scope reservations against55GiB. Do not run all harnesses or reuse receipt IDs:
obsolete whole-loop harnesses are retained to reproduce the recorded obstruction,
not recommended as a regression. `run-host.py` currently selects only attempt36;
it refuses to overwrite that completed receipt. No unchanged proof rerun is needed.

Local Lean uses the committed focused compile.py, shared mkdir admission lock,
-j1 -M4400 -DElab.async=false, and its own /tmp object overlay. Every theorem
has a #print axioms command. No existing Lean or shipped source file is edited.
