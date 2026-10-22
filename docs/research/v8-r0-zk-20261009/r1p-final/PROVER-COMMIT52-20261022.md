# Part 52: terminal dependency closure and simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit52-20261022`.
Only J10400–J10499 are authorized for proof attempts. Cold dependency work uses
separate BUILD-52 labels. No shipped crate or program source is changed.

## Stage 1: cold dependency preflight

BUILD-52-1 ran the pinned terminal-cone preflight in a dedicated host scope:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The populated host
reservation before launch was 26172456960 bytes plus this scope's 8 GiB.
The scope exited before any Lean invocation: Env J lacks both objects and
staged sources for eleven external imports. The first unresolved module is
`AspisR1SelectedMaskProbe.Funs`. Exact console and GNU-time output are retained
under `evidence/prover-commit52-20261022/build/` in the 100bit-spend-path tree.
Exit 1; wall 0.07 s; peak RSS 31184 KiB; swaps 0; source revision
`223a37671e784ddeeab6bd8295df24fdb2647a79`; axioms audit not applicable (no Lean
compile and no new theorem).

Read-only source resolution expanded the preflight to retained extraction
evidence and the retained Lean 4.32 arithmetic port. The resolver accepts
additional repository copies only when all candidate bodies have the same
SHA-256; its decisions are in `build/resolution.json`. The two missing
SelectedMask field modules use the audited arithmetic port's unchanged
`sources/` files, with original paths and hashes in `build/plan.json`.

The expanded preflight succeeds and schedules **529 missing modules**. The
single compiler pass is BUILD-52-2 (BUILD-52-1 invoked no compiler). It runs
sequentially in one scope with the same limits, asserts the actual cgroup
settings, monitors aggregate child RSS, stops near 7.5 GiB RSS or after ten
minutes without a new target, and stops at the first compiler failure. Existing
objects are reused and never overwritten. No Session A source is edited.
The J10400–J10499 launcher is prepared but no proof attempt has been used.

## Endpoint before/after

The verbatim before endpoint is preserved in this part's `endpoint/before.lean.txt`.
The deployed refinement remains explicit. No interface closure is claimed yet.
