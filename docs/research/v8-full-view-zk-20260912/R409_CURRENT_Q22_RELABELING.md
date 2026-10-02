# R409 q22 relabeling

The promoted theorem proves that relabelling the candidate domain by any permutation of `Fin (2^18)` leaves the bounded independent-answer kernel from the empty scan state invariant, after relabelling successful outputs. It applies for any block fuel, with the 64-draw cap fixed and preserves scan stopping and failure counts.

It does not prove successful-tuple uniformity, a shared memoized-oracle law, or a numerical probability claim. The next gap is successful-query mass normalization plus shared-oracle cache-hit loss.

See [R409Q22Relabeling.lean](lean/AspisV8R19/R409Q22Relabeling.lean) and [saved evidence](evidence/r409-q22-relabeling/README.md). The original compile receipt is retained; a separate read-only audit documents the R407 dependency omitted from the receipt’s empty import map.
