# Deployed caller observation and source associations — LOG D448

Work in progress. Branch `codex/pv-rj4idb-20261029`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-rj4id`, base candidate `f63ed1bd4e`.
The prior report is preserved unchanged. No crates/programs or runjoin sources
are edited. No pushes, merges, Kani, wallet/key operations or release builds.

## Scope and claim boundaries

The native observation decoder is constructed as a composition of explicit
channels, with a lossless ordered carrier and failure/divergence prefixes.
Native acquisition and old Runtime compatibility are distinguished in
[OPEN-INPUTS.md](OPEN-INPUTS.md). Actual Runtime installation is not inferred
from an abstract decoder or from a Result-only theorem.

Validation and final dispositions will be filled after the focused targets,
combined statement audit, every-new-theorem axioms audit and one final replay.
