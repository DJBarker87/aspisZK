# Failing steps

L002: own runner generated a nonexistent NHJ_NGK_exports_20261106 lookup while adapting the prefix. Direct-import object preflight stopped before Lean submission, so no proof ran. Corrected the own input path to retained NHD_NGK_exports_20261106; validation stays strict. L004 is the corrected first combined compile, not a timed-out or passing-shape rerun.

L007: own storage_domain proof treated a disjunction as a product. Elaboration fails; the resulting sorryAx diagnostic is rejected, never imported as credit. L008 cases the three actual storage constructors and proves the exact two-error domain.

L011: own result annotation used PE.AccountBorrowFailed through an abbrev, which is not a namespace. Elaboration fails and the sorryAx diagnostic is excluded. Corrected the constructor namespace in L012. No tool/cap change.

L016: own distinct packet referenced an Account abbreviation from a module it did not import. Corrected to the actually imported NGL_DistinctStep.Account and supplied local classical decidability, without changing any predecessor module. L017 is the corrected focused input.
