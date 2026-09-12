# Selected absorption-output source construction

`lean/SelectedAbsorptionOutputsSourcePolynomial.lean` constructs all sixteen
absorption outputs as chronological source polynomials.  For lane `i`, the
source value is the MLE of the literal selected absorption-row predicate for
`i`, multiplied by exactly `z[i]`.  Each coordinate slice has degree at most
two, and its Boolean table is proved equal to the lifted literal
`SelectedSemanticRows.residual (.absorption i)`.

An independent array-level expression proves the final same-index multiply
equals the constructed source value.  The pinned Rust callback computes the
sixteen selector entries through three shared `fixed/chunk_two/chunk_eight/
nodes` buckets.  Equality of that factorised bucket construction to the
literal predicate MLEs remains a separate finite selector-refinement theorem;
literal Rust/Aeneas machine semantics also remain open.

This adds sixteen outputs to the previously constructed 53/95, bringing
semantic-coordinate source coverage to 69/95.  Initial/occupancy, public
digest and public scalar outputs remain open.

The focused Lean 4.32.0 NUC replay exited 0 in 3.29 seconds, used 6,603,408
KiB peak RSS and zero swaps.  All promoted declarations print only `propext`,
`Classical.choice`, and `Quot.sound`.  Exact evidence is under
`results/v8-completion-fs-extraction-20260911/selected-absorption-outputs-source-v1/`.
