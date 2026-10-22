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

Read-only source resolution is continuing against retained extraction evidence
and the retained Lean 4.32 arithmetic port. Neither Session A sources nor
existing shared objects have been edited or replaced.

## Endpoint before/after

The verbatim before endpoint is preserved in this part's `endpoint/before.lean.txt`.
The deployed refinement remains explicit. No interface closure is claimed yet.
