# Capacity-error recovery

Automatic relaunch 1 recovered HEAD d05024ab8e and WIP sources/receipts.
57 actual one-module Lean receipts existed (001–057); 36 passes and 21
excluded development failures. No Kani, dependency build or package replay.
The previous orchestration was not running; continuation starts at 058.

The task-specific 100-attempt budget includes all 57 prior invocations.
Historical SCF/SCE budgets are separate tasks, not extra allowance here.
No unchanged failure was rerun. Stages 1–4 and the typed mismatch are retained.

The four initial paths in the request live under
docs/research/100bit-spend-path-20261013/ in this checkout; read there after
the shorter historical paths returned missing-file errors. Root AGENTS.md,
common/local rules, owner amendment and order-transport section were reread.

The first stage-5 git add met an empty stale worktree index.lock. lsof
reported no holder and no matching git mutation process was running; removed
only this worktree lock and retried the reversible staging operation.
