# Parser and multiproof source refinement

Assigned branch: `codex/cx-multiproof-cone-20261021`. The oracle-decision port
is approved for this work. Target: `OraclePortHeadlineFrozen` at
`OraclePortFrozenOrder.dV_frozen`, not the superseded recursive schedule.

## Stages

1. Pin actual parser, compact codec, leaf-batch and binary-level source cuts.
   Keep shipped files unchanged. Generate proof-only copies with an explicit
   substitution ledger; compare owned transitions under Kani.
2. Extract owned references using pinned Charon/Aeneas, preserving row and
   level recursion. Prove their mathematical meaning in new Lean modules.
3. Compose through height 18, parser sections and the reached caller, retaining
   ordered oracle addresses and ordinary rejection. Audit the exact residual
   before changing the cone classifications.

## Proof boundary

A passing one-step certificate is not a whole-loop certificate. Equality of
roots is not equality of ordered oracle logs. The scratch suffix and writes
made before rejection must be retained where observable in the source cut.
The global `AcceptedRunJoin` still requires the other cones and the frozen
source/model caller identities. No whole cone is declared complete here yet.

## Resources and evidence

Host workspace: `/home/dombarker/project-offloads/codex-cx-multiproof-cone-20261021`.
Host jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 after
reservation preflight. Rust gates are optimized. Local Lean uses one process,
the shared mkdir lock, `-j1 -M4400 -DElab.async=false`, and a private object
folder. Every compile/proof attempt records target, revision, source/dependency
hashes, exit, wall time, RSS, swaps, and axioms (N/A for Rust).
