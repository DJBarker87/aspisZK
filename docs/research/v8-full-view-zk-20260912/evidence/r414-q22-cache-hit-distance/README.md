# R414 q22 cache-hit distance evidence

For any horizon, source state, starting scan state, cache table, and result observer bounded in `[0,1]`, the theorem bounds the difference between the lazy q22 projected-result mean and the uniform-candidate kernel by an explicit `hitMass` term: the independent mean of `guardFresh` ending in `none`. The challenge theorem specializes to eight blocks, with the 64-draw cap fixed from the empty scan state. No whole-program `FreshFrom` premise is used, and cached reads are not resampled.

The comparison is on the projected `Except Nat (List Nat)` result, preserving failure counts; it does not assert equality of full trace or transcript-state distributions. It does not bound source-specific hit mass, prove full source-prefix correspondence, or give a numerical security bound. The remaining bridge must bind the actual initial state, adversary cache, callback, and retry chronology and bound `hitMass`; normalized legal-query support from R412 remains open as well.

The single saved run exited 0 in 1.28 seconds with 3,225,496 KiB GNU-time Lean-child peak RSS and zero swap under the recorded `5G/7G/0 swap/128 tasks` scope with `-j1 -M4500`. Both full axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. Direct dependency sources and post-run cached object hashes are saved separately. `verify_evidence.py` is read-only.
