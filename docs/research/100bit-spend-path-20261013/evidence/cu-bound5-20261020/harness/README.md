# Frozen-ELF CU campaign harness

Host root: `/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020`.
Source is copied from the freeze workspace, with all 58 frozen source hashes
checked by `source_check.py`. `driver/` and `component_checks.rs` are the
native measurement inputs inherited from bound3, built against frozen source.
The trace crate is the same driver with `trace=["litesvm/register-tracing"]`.

Run each executable gate in its own systemd scope:
`MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64`.
Check populated reservations using `reservation.py` before adding scopes.
Native compilation is release, offline, locked, `-j 4`, with
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. `build-sbf.sh` separates direct
SBF linker flags and uses `linker-bin/cc` to cap host proc-macro links.
`capped.py` records command/exit/wall/RSS/swaps; `sweep.py` records every
native execution separately and refuses repeated completed labels.

Order used:

1. `pins.py`, six control replays, `check-controls.py`, frozen verifier
   rebuild, driver/trace builds, profiling/line-table builds. Pool is
   independently rebuilt and pin-checked as well. Existing build caches
   are reused; no verifier source is modified.
2. `replay_plans.py` produces the grid/target/random replay plans from the
   retained bound3 proof/public corpus. The exact executed plans are in
   `../plans/`; `corpus_inventory.py` verifies the inherited OS masks and
   every proof SHA. `sweep.py` measures each new-ELF execution.
3. `pick_traces.py` chooses per-variant CU/position extrema; add the
   predecessor geometry/duplicate targets, then `make_trace_plan.py`.
   `trace_controls.py` adds six saved-control traces. `make_profile_plan.py`
   replays twelve measured inputs with the attribution ELF.
4. `audit-final.sh` checks all 70 trace labels, runs `run_audit.sh` under
   a capped receipt, maps source lines by equal instruction bodies, and
   produces the provisional classification. Its historical rule snapshot
   is not a final bound. Raw CFG and line-map data stay on the host, pinned
   in `../retained-analysis.json`.
5. `analyze-final.sh` always regenerates matched-address rules from bound3,
   adds `frozen_rules.py` code-cited caps/exclusions, computes residuals,
   SHA charges, phase attribution, B, variants and independent validation.
   `new_path_audit.py` checks every executed branch and loop of the
   refactored paths, including the three first-key checks. The report
   discloses the conservative pre-exclusion result and source argument.
6. After validation, `cleanup_traces.py` hashes/removes only `.regs` and
   `.insns` in this task's trace directory. All keys and proof sidecars
   remain. `export_final.py` serializes text evidence only. A compressed
   intermediate used during packaging was replaced by compact text JSON;
   no binary archive is part of the committed evidence.

`sites-per-variant.json` has a `columns` schema and one row for every site
classification, including zero residuals. `sites.json` gives full source
citations, detailed dominating-variant costs and compact trivial-site groups.
The release verdict uses only admitted split 10, following the lead's ruling.
Rejected split 11 is never counted as accepted coverage.
