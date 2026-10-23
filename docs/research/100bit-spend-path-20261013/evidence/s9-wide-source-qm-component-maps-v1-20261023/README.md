# Source Wide QM add/sub maps

This packet records isolated same-call Result maps: the transparent source Wide extraction cut's `QM31.add` and `QM31.sub` map to explicit componentwise CM operations in the actual QMMul cut. Each preserves success, failure, and divergence. The subtraction proof converts the CM-map function head before applying generic bind transport; earlier broad elaboration attempts are recorded as diagnostics only.

Both accepted targets exited 0 with zero swap. Their `#print axioms` reports contain only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). Compiled objects are omitted. This packet does not establish the full WideExact multiplication map or refinement to checked CurrentWide operations.
