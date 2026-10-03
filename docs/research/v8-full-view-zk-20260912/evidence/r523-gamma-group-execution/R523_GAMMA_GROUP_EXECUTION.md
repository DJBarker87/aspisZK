# R523 gamma group execution

Final target `AspisR523GammaGroupExecution/R523GammaGroupExecution.lean`,
source SHA-256 `e9fca7178328a6af15593f8f82e57391f3c932d52a87214e8004788ebd6721ac`,
compiled on source revision `1d01ab5c3e43eac493f11b105fdaaf297e9b28cb` with exit 0, wall 0:01.64,
peak RSS 3,704,992 KiB, and zero swap. The canonical Lean file is byte-identical
to the final focused source. The exact source, receipt, raw log, and complete
`#print axioms` output are preserved in `focus-records/`.

`checkedMac_foldlM` proves that a list of at most four bounded U64 operand
pairs executes through `List.foldlM checkedMac`, returns the same natural
accumulator, and stays within its indexed prefix bound. `checkedMac_four_terms`
specializes it to the selected four `Fin` terms starting at zero. Both complete
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

All focused attempts are retained: first failure `1791055345778723000`, the
intermediate green list lemma `1791055359151101000`, and final selected-four
specialization `1791055481030534000`. The first failure records the rejected
nonempty-list count normalization; no unchanged target was rerun.

This proves bounded list-level U64 arithmetic only. It does not prove native
array or slice-loop execution, optimized Rust group execution, storage/frame
behavior, or whole preparation/callback correspondence. The first remaining
source obligation is the actual selected group loop and its storage/frame
behavior.
