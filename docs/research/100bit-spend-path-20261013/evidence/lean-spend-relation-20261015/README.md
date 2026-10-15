# SpendRelation focused Lean target

This bundle preserves the green focused compile of `R1SpendRelation` and the direct imported objects used by its source. The module defines the explicit spend witness/relation, the executable concrete M31 checker, and four theorems audited in the target log. The four axiom reports are `[propext, Quot.sound]`. The compiler emitted benign unused-section-variable warnings for `DecidableEq K` in `input_note_extracted` and `integer_bounds`.

The target source imports `R1InputWitnessCheck`, `PublicOptionShape`, and `AspisV8R15.ExactTowerBase`. Their source/object hashes and paths are recorded in the manifest. The package also preserves the `R1InputWitness` and `R1SpendSemantics` source/object pins used by the adjacent `SpendRelationExtraction` draft so its import availability can be checked without compiling it. `R1InputWitnessCore` and the broader transitive environment are supplied by the pinned Lean path and are not claimed as a closed transitive archive here.

Attempt `spend-relation-a`: exit 0, 1.96 s, 3,342,520 KiB maximum RSS, zero swap; `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. No rerun was performed.

`SpendRelationExtraction.lean` is not compiled by this bundle. Its three import module objects (`R1SpendRelation`, `R1InputWitness`, `R1SpendSemantics`) are present and pinned. This is an import-availability observation, not a validation of its theorem proof.
