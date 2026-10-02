# R413 guarded oracle distance evidence

The final theorem gives a general comparison bound. For any finite nonempty answer set, any address type with decidable equality, any causal program, any memoization table, and any observer of the full trace/result whose values lie in `[0,1]`, the absolute difference between `lazyMean` and `independentMean` is at most the independent mean of the `guardFresh` indicator for terminal `none`.

No `FreshFrom` premise is assumed; cached reads are not resampled. The guard is a comparison experiment, not a modification of the source program. This proves no numeric guard-hit bound, source freshness statement, or security result. The remaining obligation is to bound guard-hit probability for the actual source, including initial state, adversary cache, retries, and the full callback.

Both attempts are retained. The final run exited 0 in 1.62 seconds with 3,237,940 KiB GNU-time Lean-child peak RSS and zero swap under the recorded `5G/7G/0 swap/128 tasks` scope with `-j1 -M4500`. All seven complete axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The direct source dependency and a separate read-only cached-object identity are recorded; `verify_evidence.py` does not run Lean.
