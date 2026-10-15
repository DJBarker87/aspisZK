# SpendRelationExtraction focused Lean target

This bundle preserves the green focused target `R1SpendRelationExtraction`, its source, receipt, output/time logs, runner pins, and the imported object pins. The target proves an existential generic-field bridge from the existing production trace facts to the explicit `SpendRelation` witness. Its `#print axioms` report is `[propext, Classical.choice, Quot.sound]`. The two reported `change variantOutput pub w` no-op warnings are retained as emitted.

The imports `R1SpendRelation`, `R1InputWitness`, and `R1SpendSemantics` are present as cached modules and pinned in the manifest. Their listed source snapshots are current repository sources; they are not asserted to be complete transitive source provenance for all imported cached dependencies. The direct supporting modules `R1InputWitnessCheck`, `PublicOptionShape`, and `AspisV8R15.ExactTowerBase` and objects are also recorded and archived.

Attempt `spend-relation-extraction-a`: exit 0, 1.77 s, 3,331,524 KiB maximum RSS, zero swap; `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. This remains an existential generic-field statement; the bundle makes no efficient-extraction, byte-parser, or Rust-refinement claim.
