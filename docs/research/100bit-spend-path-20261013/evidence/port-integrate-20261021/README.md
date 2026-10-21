# Oracle port integration merge gate — 2026-10-21

PASS on branch `codex/cx-port-integrate-20261021` at source revision
`ec56a3486e83a1071f423fda2579c1b21e4e0349`.
The rebased research pin is `8e4931b1f72f86fafdb10d5f4499ed686e1847d0`.
No Lean source fix was necessary. Only receipts and their local runners were added.

All 119 port modules in the requested import closure compiled once, in dependency
order, into `/tmp/codex-cx-port-integrate-20261021-objects`. Existing non-port
objects were reused. Aggregate measured compile wall time: 909.166 s;
maximum per-attempt RSS: 3691790336 bytes; total swaps: 0.
Every attempt used Lean 4.32.0, `-j1 -M4400 -DElab.async=false`, the shared
mkdir lock and `/usr/bin/time -l`. No package build or unchanged replay ran.
The explicit local-Lean instructions override the older remote-only common rule.

`manifest.json` records every command, source revision/hash, direct-import object
hash, dependency fingerprint, exit status, wall time, peak RSS, swap count and
full axiom output. Each attempt also has its source snapshot, command, receipt,
Lean log and time log. `targets.csv` gives results for every compiled module.
No object files or binaries are committed; private objects are retained for reuse.

Both `AspisR1.OraclePortHeadlineFrozen.final_soundness` and `per_query` report
exactly `[propext, Classical.choice, Quot.sound]`. Their shared module exited 0
in 4.178 s, with 3691790336 bytes peak RSS and zero swaps. Its existing warning
about exponent 454 remaining unevaluated is benign; no threshold was raised.
All other printed axiom sets are subsets of the same allowed set.

| Requested module | Result | Wall (s) | Peak RSS (bytes) | Swaps |
| --- | --- | ---: | ---: | ---: |
| OraclePortFrozenOrderHeadline | PASS (exit 0) | 4.178 | 3691790336 | 0 |
| OraclePortCkptAbiCodec | PASS (exit 0) | 4.811 | 3518300160 | 0 |
| OraclePortCkptAbiFreeze | PASS (exit 0) | 10.049 | 3555065856 | 0 |
| OraclePortCkptAbiReadSequence | PASS (exit 0) | 2.435 | 2260828160 | 0 |
| OraclePortCkptAbiReader | PASS (exit 0) | 3.734 | 2243903488 | 0 |
| OraclePortCkptAbiReference | PASS (exit 0) | 5.168 | 3649929216 | 0 |
| OraclePortCkptAbiRejection | PASS (exit 0) | 4.448 | 3555868672 | 0 |
| OraclePortCkptAbiSource | PASS (exit 0) | 2.906 | 2297692160 | 0 |
| OraclePortCkptAbiSourceBacking | PASS (exit 0) | 2.093 | 2243903488 | 0 |
| OraclePortCkptAbiSourceFields | PASS (exit 0) | 5.202 | 2484944896 | 0 |
| OraclePortCkptAbiTry | PASS (exit 0) | 2.141 | 2247835648 | 0 |

`audit.json` scans all 366 new `.lean` files (including historical evidence
snapshots): no sorry, axiom declaration, admit tactic, native_decide,
implemented_by, or extern attribute. The 187 code occurrences of `admit` are
reviewed references to the `OraclePortAdmission.admit` decision wrapper, including
its definition, and are recorded with source lines. Comments/string hits are
retained separately for review.

All pre-existing files are byte-identical to the pinned research tree, and
`crates` and `lean-candidate` have no changes at all. Research advanced during
this job to `acb9e4c9d676453a3cd296705ea4e0402d30b731`; the two later commits add
unrelated S4 evidence and update a design handoff. No shared protected Lean,
candidate, or shipped crate file differs from that newer tip either.
`research-movement.json` records the exact movement. The worktree was not merged
or rebased during verification.

`plan.json` records the source import graph and cached dependency hashes;
`cache-source-audit.json` links cached objects to successful matching source
receipts wherever available (226 matches, no conflicting recorded source hash).
This is cache reuse, not a fresh rebuild of the historical dependency tree.
Two source-graph names (`R1SelectedChallengeMapCore`, `R1UnifiedSamplerPublic`)
have no standalone cached object; they are behind cached historical modules and
are not required as direct imports by any compile in this gate.

Reproduction: run `preflight.py`, then `run.py`, then `finalize.py` from
`tools/port-integrate/`, using the retained caches. The runner refuses an
unchanged source/dependency retry. Do not rerun a successful gate without a
new source/environment input or an identified missing evidence artifact.
These remain conditional endpoint proofs; no source adoption premise is removed.
