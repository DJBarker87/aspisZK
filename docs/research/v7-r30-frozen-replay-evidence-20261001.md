# V7 R30 frozen closure replay

The first driver attempt at `2d1646ee5` stopped before compiling any module:
Lean required an explicit source root for a source outside the backend cwd.
Exact failed target `V7CallerCurrentReleaseR26.TypesExternal`: exit 1,
0.39s, peak 803856KiB, swaps 0. Driver aggregate exit 1, 1.01s,
peak 804176KiB, swaps 0. Remote log retained at
`/home/dombarker/project-offloads/v7-r30-closure-20260930/replay-2d1646ee5.log`.

Replacement driver supplies the generated/proof/staged module root with `-R`,
asserts the actual cgroup limits, and records cgroup memory peak/events on exit.
No Lean proof changed, no cap was raised, and no memory failure occurred.

Focused replacement preflight (`2d1646ee5+driver-fix`):
`V7CallerCurrentReleaseR26.TypesExternal`, exit 0, 1.76s,
peak 2534600KiB, swaps 0. Aggregate exit 0, 2.47s, peak 2534600KiB.
Cgroup peak 380964864 bytes, swap current 0, all memory pressure/OOM events 0.
Actual limits: high 7516192768, max 8589934592, swap max 0 bytes.

Frozen manifest SHA256:
`756adb168b68fd25ae1ace739ace2ef30b80638cf71b2633d74de6d9f7782fca`.
Order SHA256:
`291eedb3eb801f74510ad509d3592ee0e682b190060cb7d3570e45f19da6c0ef`.
Driver SHA256:
`58ac8616229f4860a1c70f8e03fb8f67856d3f18354e47875c359655ab68b3ec`.
Manifest validation is green for 336 transitive source modules; staging checks
all 142 callback sources against the previously frozen aggregate.

## Final result: passed

Source revision `d62c8dea4`. Exact target:
`V7ProductionSnapshotObserverR30ClosureAxioms`, covering all 336 transitive
source modules. Every module exit was 0, and every recorded swap count was 0.
Aggregate exit 0, wall 1318.42s, maximum child RSS 7303996KiB
(the `V7CallerCurrentReleaseR30CircleAccumulator` target). Final audit target
exit 0, wall 3.81s, peak RSS 7146236KiB, swaps 0.

Actual cgroup peak was 1204023296 bytes; swap current was 0. Memory high/max/
swap-max remained 7516192768/8589934592/0 bytes. All memory event counters
were zero, including high, max, OOM, OOM kill, and group kill. No cap increase,
resource-pressure restart, or unchanged complete regression was performed.
There was one successful complete replay, after the explicitly documented
source-root driver correction and smallest-target preflight.

The final audit printed the scanner, packed decoder, packed gamma, normalized
polynomial, observer query values, running claim, terminal composition, and
production acceptance closure. Every audited theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

Final critical bridges:

| Target | Exit | Wall s | Peak KiB | Swaps |
| --- | --- | --- | --- | --- |
| V7ProductionSnapshotObserverR30RunningCanonical | 0 | 4.82 | 7213140 | 0 |
| V7ProductionSnapshotObserverR30TerminalClosure | 0 | 14.25 | 7243592 | 0 |
| V7ProductionSnapshotObserverR30ProductionClosure | 0 | 4.28 | 7206680 | 0 |
| V7ProductionSnapshotObserverR30ClosureAxioms | 0 | 3.81 | 7146236 | 0 |

The full per-target timings, RSS, swap counts, exact source paths, Lean version,
manifest hashes, axioms prints, and cgroup evidence are retained in
[the replay log](v7-r30-frozen-replay-d62c8dea4-20261001.log), SHA256
`17a42183f98bc92fe9e15a84ff7e62d56312e594aadc2666283bfb2b96ce2552`.
Remote workspace:
`/home/dombarker/project-offloads/v7-r30-closure-20260930`, with successful
compiled output in `replay-d62c8dea4` and original failed-driver evidence kept.

The missing V7 source decoder/callback canonicality and terminal-relation chain
is now checked from literal production observer acceptance. This closes the
previously unproved `runningCanonical` premise without assuming it. Scope and
remaining cryptographic/source-extraction boundaries are stated in
[the closure evidence](v7-r30-production-terminal-closure-evidence-20260930.md).
No new Fiat--Shamir or probability/soundness claim is made.
