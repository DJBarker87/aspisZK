# Frozen stage-2 inventory

Run `python3 -B docs/research/100bit-spend-path-20261013/tools/stage2-extraction-kit/inventory.py --check`
from this worktree to verify the committed source-cut inventory, frozen Git
blobs, exact stage-1 fragment matches and predecessor receipt/root pins.
`inventory.py` without `--check` regenerates those files. It never invokes Rust,
Charon, Aeneas, Lean, SSH, SBF or runtime gates and never edits verifier source.

This is stage 1 of the assignment. The pinned-tool finish-relation blocker and
corrected diagnostic caller/resume failures already exist. No unchanged build
is rerun and no failed/synthetic candidate is promoted to a frozen-source
extraction. See the design/report for the required lead decision.
