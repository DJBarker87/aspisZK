# Well-formed fresh-oracle producer

`lean/FSV8WellFormedFreshOracle.lean` defines `WellFormedFreshOracle` with
history/total coherence, fresh-count coherence, no programmed table entries,
and unique table inputs. Query and bounded `runMachine` preserve this
predicate for an arbitrary `AdaptiveController`; programming operations are
separate and intentionally excluded.

For any empty-state controller run with an explicit bound
`freshCalls ≤ steps`, the leaf constructs a finite tape directly from the
chronological fresh-answer history, pads it with a fallback, and proves
`run_from_empty_projected_state_aligned`. This yields the projected current FS
state and `StateAligned` without supplied fresh-history-content or
projected-prefix premises.

The result is deterministic only. It does not assert uniformity, probability,
independence, deployed-ROM coupling, or correctness of a programmed fork.

Evidence: pinned Lean 4.32.0 NUC compile, `-j1 -M8192`, exit 0, wall 3.58 s,
maximum RSS 6,530,856 KiB, swap 0. Source SHA256
`2a65d06ec6f5d8ded21b097600f487f2ea0e6cf2c608577347b43a739fb6947e`;
OLean SHA256
`d73a4ba1ab5ac35cc603a2e0a8a3258ee5b1cbf55838e6a42949b8c5b103a4a7`.
The promoted corollary reports `[propext, Quot.sound]`.
