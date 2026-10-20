# Candidate-ELF CU campaign harness

Host root `/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020`.
Source copied into this isolated workspace, then overlaid with the 59 exact
candidate inputs; `source_check.py` verifies the prep5/c16e59e77 binding.
No production source is changed. Caches are copied, never shared for writing.

Every executable/analysis gate has its own scope: MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Check populated reservations
before adding 8 GiB; stay within 55 GiB total. Native Rust is release,
offline/locked, -j4, `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.
SBF uses `--threads=4` directly and the native cc wrapper for proc macros.
`capped.py` and `sweep.py` retain per-gate/per-run receipts and refuse
repeating completed work. Ordinary text/source inspection needs no build.

Executed order:

1. Default/devnet/Pool SBF rebuilds, `pins.py`, native sweep/trace driver
   builds. Default/devnet text and two-slot ID reconstruction must pass.
   Profiling and line-table variants are attribution-only separate builds.
2. `prepare_plans.py`, six controls and `check-controls.py`, grid, targets,
   random-a/random-b. The exact original OS-masked corpus is reused via
   proof/public sidecars; `corpus_inventory.py` verifies all bytes.
3. `prepare_traces.py` selects 48 grid extrema plus inherited geometry/
   duplicate targets and the complete-corpus per-variant maxima. Four
   complete-corpus settlement extrema were appended to the running plan;
   `finish-tracing.sh` waits for the original worker, resumes only the four
   new labels, and audits all 74 traces. Twelve `make_profile_plan.py`
   replays supply phase logs. Component Rust checks run optimized.
4. `audit-final.sh` freshly derives every CFG/arm cost from candidate ELF
   and register traces and maps source lines via equal instruction bodies.
   `analyze-final.sh` reattaches only strict instruction-matched predecessor
   rules, applies current `candidate_rules.py`, derives per-site residuals,
   parent-SHA charges, phase attribution, B and complete-corpus variants.
   `new_path_audit.py` supplements complete per-variant branch coverage.
5. `enrich-canonical-caps.sh` adds directly checked ELF counters for two
   canonical-scan headers with missing line numbers; asserts B is unchanged.
   `finalize_metadata.py` refreshes current-definition citations and asserts
   every operational exclusion/cap selector/value and every B is unchanged.
   No additional ELF or corpus replay occurs in these metadata checks.
6. `package-final.sh` checks artifacts, hashes/deletes only task `.regs` /
   `.insns`, retaining keys, proof/public sidecars, raw CFG and build caches.
   `package_check.py` checks all completed receipts, deleted-trace inventory,
   and 1,664 retained task keys. `export_final.py` exports only text evidence,
   after the scope's own receipt has completed.

`analysis/sites-per-variant.json` has an explicit compact columns schema and
all 26 role/variant rows, including every zero residual. `sites.json` has
full cap/exclusion/source references. `variants.json` uses the complete
746-input corpus. Large raw CFG/line maps remain pinned on host via
`retained-analysis.json`. Plans and source/harness pins permit review without
publishing proofs, signing keys, executables or compiled objects.

The method's positional and inclusive-callee assumptions remain those of
reviewed bound4; this is not a formal CU theorem. Split `[3,10]` is the
sole admitted stage-1 split. See `../REPORT.md` for the exact verdict/scope.
