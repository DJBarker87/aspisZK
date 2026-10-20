# S3 extracted `Variant::row` output equation

This focused packet proves the value returned by the selected S3 non-D row loop. The exact extracted loop first gets a `d < 5` continuation step, then preserves a symbolic accumulator invariant over the processed TAU entries. The final OR-fold is converted to the arithmetic row formula by four applications of `Nat.two_pow_add_eq_or_of_lt`, using symbolic bounds for the disjoint two-bit fields.

The final checked theorem is `AspisR1.S3VariantRowAeneasCut.s2_row_result_value_current`: for every `j : Usize`, `s2_row_result j` returns successfully and its output value is exactly `S3S9CurrentSourceModel.s2Row j.val`. The small `s2Row_source_cut` declaration is checked byte-for-byte after whitespace normalization against the original `s2Row` RHS, and the theorem is also compiled against the retained source-model OLean owner (not only the copied definition).

This closes the extracted row-loop output equation. It does not establish the surrounding `Weights::pair` caller, S3 row classification, adoption/runtime correspondence, or end-to-end protocol claims. The selected proof owners use standard Lean axioms only. No OLean, IR, executable, or cache object is included.

Run `python3 check_source_cut.py` from this directory to verify the extracted source declaration body.
