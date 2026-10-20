# S4 outer fold trace V2

This source-only packet records the green outer-loop trace with per-batch source witnesses and the actual reducer-residue theorem. The strengthened `ExactTrace` stores the same `BatchWitness` returned by the source-shaped batch theorem, including its `ActualTermTrace`, at-most-four term count, per-product caps, and exact limb delta. The public reducer theorem proves that each final accumulator cell is reduced to the sum of those exact parsed products modulo the M31 modulus.

The packet is a source-model result. It does not establish that the frozen Rust caller reaches this loop, nor Rust `StepBy`/`from_fn` equivalence or the complete four-dot output relation. The separate output-residue-aligned packet covers N8 output construction on the same loop limbs; the next consumer must compose those witnesses without replacing the returned array or inputs.

The V2 source and successful Lean receipt are captured under `sources/` and `evidence/`. Selected producer source and receipts are snapshotted under `dependencies/producers/`; object files are deliberately omitted. Earlier V2 attempts are retained under `evidence/diagnostics/` and are not release evidence.
