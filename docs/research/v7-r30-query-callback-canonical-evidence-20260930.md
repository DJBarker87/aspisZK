# V7 R30 literal query callback canonicality

Source predecessor: `b7c2877ea`; checks used this revision plus the exact
source hashes below. Remote pinned Lean 4.32 cache; each target ran in its own
`systemd-run --user --scope` with MemoryHigh=7G, MemoryMax=8G, MemorySwapMax=0.
Only one 8G scope was reserved at a time.

| Target | Exit | Wall seconds | Peak KiB | Swaps | Source SHA256 |
| --- | --- | --- | --- | --- | --- |
| V7ProductionCallbacksR30FromFnCanonical | 0 | 1.73 | 2682444 | 0 | fc81b192759befe07cdf6c51d6335a450371fd56fa6b3ea03b2618322e0e9c98 |
| V7ProductionCallbacksR30QueryGammaCanonical | 0 | 1.96 | 2694104 | 0 | 1a16b2c65f5be90c770bfff4db1e2c8e56415d43254a8b8ccee6fe8bb992fa6b |
| V7ProductionCallbacksR30FoldQueriesCanonical | 0 | 1.72 | 2684512 | 0 | 2cb7dfbc9b6a7ea5d8143432b756fb47fd4791749da9cc53151f39cb9d0864eb |
| V7ProductionCallbacksR30QueryValuesCanonical | 0 | 1.79 | 2689316 | 0 | 37cffaec6dfbc4cebabad7eb1f456d121062b260c00938fa18d6592850e21148 |

`#print axioms` for each exported successful callback theorem reported only
`propext`, `Classical.choice`, and `Quot.sound`.

The source query-opening loop preserves canonical rows through successful
packed decoding and gamma combination. The generic source `from_fn` recursion
lifts the normalized polynomial callback to all sixteen folded query values.
The production observer wrapper retains these values from the literal callback
invocation; no arithmetic callback is replaced by a validation-prefix surrogate.
These results prove representation canonicality, not a new polynomial identity,
overflow-freedom guarantee, or cryptographic soundness claim.

Mechanical failed preflights: query rows initially hit duplicate scalar-literal
elaboration obligations (exit 1, 2.04s/2684688KiB); introducing a named zero row
fixed them. Fold preflight lacked local Inhabited instances (exit 1,
1.73s/2670164KiB). Query-values preflights exposed missing/ambiguous/different
default instances (exit 1, 1.84s/2676336KiB, 1.69s/2677196KiB,
1.84s/2677884KiB); the final theorem uses the exact fold instance. No resource
failure occurred, no cap was raised, and no full manifest was run.

Remaining work: retain the first relation polynomial's source evaluation,
derive query insertion running-claim canonicality, and compose the terminal
source theorem before the final frozen replay.
