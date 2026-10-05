# R807 active diagonal block binding evidence

This package records the focused proofs tying the selected-source matrix to certificate diagonal blocks for fixed selected witness parameters. There are 38 active-only blocks with indices 02–40 excluding 06. Block 01 is the previously proved equality and unit determinant. Blocks 00 and 06 are not proved here.

The split proof covers 173 row equalities across the 37 blocks excluding block 02, with block 02 preserved from its earlier green proof; this totals 176 rows. Each active row equality was compiled separately or in a two-row small-block module. Each block aggregation uses the pinned generic `finN_ext` lemma and the named row-equality facts.

The final aggregate axioms are recorded in each run receipt. Green outputs use the standard `[propext, Classical.choice, Quot.sound]` set (the exact output for every declaration is included in the receipt); there is no `sorryAx` in green proofs. Failed aggregation attempts are retained with their exact sources and logs. In particular, the initial block-04 aggregate exceeded the pinned 4500-MB Lean memory limit; its replacement used finite-function extensionality and compiled successfully.

This establishes only source-to-certificate diagonal block equality at these fixed selected parameters. It does not prove the lower off-diagonal zero block, settle exceptional blocks 00/06, imply global rank, or prove privacy or soundness.
