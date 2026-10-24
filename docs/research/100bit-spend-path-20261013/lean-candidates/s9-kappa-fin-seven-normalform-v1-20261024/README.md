# Same source kappa polynomial in Fin7 normal form

The existing Nat-range7 kappaPolynomial of arbitrary native parts equals the Fin7 polynomial of the SAME parts. The proof reuses existing Fin.sum_univ_eq_sum_range and then the bounded kappaTerm branch. partAt reads the native array list at the Fin7 coordinate directly, avoiding machine index constructors and their hidden proof arguments.

No canonicality, model values, accepted source execution or replacement coefficient vector is supplied. No seven-cell concrete expression is unfolded. The first actual theorem check passed; an earlier import-only failure is retained and was repaired by staging exactly three missing accepted cached objects. See receipts and selected-owner evidence. This is a source definition equality, not soundness or whole-component closure. No binaries.
