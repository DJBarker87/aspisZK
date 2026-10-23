# S9 QM square prefix to extracted source cut

This focused packet proves that the three `QM31.square` calls reached in one successful concrete active-body prefix are the corresponding successful calls in the extracted square source cut. The theorem consumes the same `BodyPrefixWitness`, derives canonicality for `q2` from its successful `kpowers` read and for `q4`/`q8` from its high-array reads, and inverts the accepted full-Result helper bridge to recover the exact cut outputs `toCut q4`, `toCut q8`, and `toCut q16`.

The result is a same-run operation-prefix correspondence. It does not prove equality of the entire body or loop under a changed operation record, nor a deployed-binary refinement.

The Lean run was exit 0 in 16.037 seconds with 3,219,374,080 bytes peak aggregate RSS and zero swaps. The source and object hashes and full process metrics are in `proof/receipt.json`; both exported theorem axiom reports are retained in `proof/lean.log` and use `[propext, Classical.choice, Quot.sound]`. Compiled objects are not included.
