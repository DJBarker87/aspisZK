# R0 source-locked baseline

Date: 2026-09-13. Branch: `research/v8-privacy-repair-20260913`.

Pack checks:

- `python3 tools/verify_manifest.py`: exit 0, 41 files, 0 failures.
- `python3 tools/run_checks.py --stage python`: exit 0; 36 Python tests and
  source reconstruction pass.
- `python3 tools/verify_source_pins.py --repo
  /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913`: all six
  immutable pin checks pass. This verifies Git object identity only.

Actual source regressions added to the isolated branch:

- `circle_candidate::v8_q22_same_public_local_separator::fixed_pair_4_6_exposes_same_public_selection_row`:
  exit 0, one test passed. It checks the q4/q6 separator against the actual
  Rust circle encoder and reconstructed relation-free mask inventory.
- `pool_v1_pair_forest_honest::tests::diagnostic_same_public_duplicate_input_selection_pair`:
  exit 0, one test passed; optimized `cargo test --offline -p aspis-prover
  --release --lib ...`, wall 7.69 s, peak RSS 555,679,744 B, zero swaps.
  It compiles both duplicate-commitment witnesses, confirms equal public
  statement/snapshot, applies actual mask material with distinct seeds, and
  preserves the q4/q6 functional distinction.

The existing q22 row-1014 `{1,2}` certificate remains separate from this
column-zero `{4,6}` regression. These results are negative/raw and valid-trace
evidence only. They do not establish joint-view coverage, simulator
construction, adaptive retry privacy, or a repair.

Remaining R0 blocker: the source reconstruction still has three missing old
artifact preimages, and the complete generated q22 publication call graph is
not yet source-linked to a production adapter. No repair claim is made.
