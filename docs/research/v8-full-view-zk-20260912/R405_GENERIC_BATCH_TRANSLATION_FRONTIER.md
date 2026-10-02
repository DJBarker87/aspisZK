# R405: generic batch translation frontier

R396 successfully extracted the selected generic batch and preserved a structured body for `Iterator::try_fold`, including `Try::Output = B`. Its saved LLBC contains no erased-region occurrences in that declaration. R398 passed that exact LLBC unchanged to the pinned Aeneas R385 v2 binary, which exited 2 before generating Lean output. The failure is at an explicit Aeneas signature assertion requiring `trait_type_constraints = []`; the retained associated-type equality therefore remains unresolved by this translation route.

The evidence bundle at [r405-generic-batch-translation-frontier](evidence/r405-generic-batch-translation-frontier/) contains the original R394–R398 artifacts, receipts, logs, source and toolchain hashes, plus the exact content-addressed Aeneas source file and assertion excerpt. R394/R395 are read-only provenance inventories. The bundle verifier is included there.

This is an extraction/translation diagnostic only. It proves no Lean theorem and establishes no Rust execution, iterator, callback, cryptographic, or security correspondence. The next technical frontier is an equality-preserving way to represent the generic associated-type constraint, followed by proof of the remaining standard-library dispatch/`next` and full callback behavior. No replacement semantics are assumed.
