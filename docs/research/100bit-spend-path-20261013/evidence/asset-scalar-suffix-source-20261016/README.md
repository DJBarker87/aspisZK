# Complete asset and withdrawal scalar suffix

`ScalarSuffixPacking.actual_scalar_suffix` derives successful execution, canonical output and the exact contribution of the two retained asset-family residuals at slots92/93 to every packed output cell. Its source-order suffix includes the actual opening reads at1/10, two lift_m31 calls, checked row arithmetic44/508/460/1010, actual boxed selector rows, subtraction/multiplication and all scalar_lanes variant/presence branches, followed by the actual preweighted call at92. Operation success, scalar residual identities and packing success are derived.

Inputs are a canonical point, its successful boxed selector result, canonical openings.z and incoming packed cells, real M31 bounds on the source asset and unwrapped withdrawal amount, and the three public-field correspondence equations used by this family. Public amount/asset bounds must still be supplied by the admitted caller; arbitrary U32 words are not assumed canonical.

`ScalarSuffixSlice` retains the exact suffix cut from the sealed generated semantic_packed declaration, with recorded helper qualification and packed-variable renaming. Its scalar_values helper cuts only the final packing call; suffix_eq_values proves that decomposition. The source generator records the raw declaration hash, exact suffix offsets/hash, substitutions and output hash. Integration of this proved suffix with the complete generated semantic_packed caller remains due; no whole terminal theorem is claimed here.

`SemanticPublicModel` provides one shared exact-field interpretation of every actual source public field, including optional digests/withdrawal amount, next pair index and both frontier arrays. It defines natural casts of source words; it does not assert their canonicality or custody.

The proof reuses the old same-boxed row, read16, exact arithmetic, scalar-lane branch, generic field transport and preweighted list theorems. A concrete comparison timeout was replaced by a generic family_literal lemma over arbitrary fields that normalizes only the four small Fin indices, plus structural aliases and a named start-index rewrite. No resource or heartbeat limit was raised.

All focused targets exited0 on the capped NUC with zero process swaps. The theorem reports contain only standard Lean axioms; source-slice/public-definition targets have no theorem reports. Exact commands, target/source revision, source/object/import pins, reservations, wall/RSS/swap and axiom reports are retained. No broad replay or runtime regression was repeated. Whole verifier/caller, full accepted-spend soundness, privacy and release-artifact correspondence remain open.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `ScalarSuffixRows` | 1.55 | 3745388 | 8 |
| `ScalarSuffixSlice` | 1.775 | 3973640 | 0 |
| `ScalarSuffixExecution` | 2.068 | 4004968 | 1 |
| `SemanticPublicModel` | 1.52 | 3973172 | 0 |
| `ScalarSuffixPacking` | 2.055 | 4001116 | 4 |
