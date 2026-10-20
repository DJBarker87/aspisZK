# Candidate 12 caller inputs checked

The whole emitted resume weight loop now proves canonical decoded weights, exact length and unchanged input bytes. The loop is actual source with exact Reader.k/raw inlining and an inverse substitution check; its symbolic handback proof avoids concrete 64/256-element reduction.

The pinned std empty-vector reservation wrapper proves the length frame for arbitrary RawVec outcomes. Together with actual heap fill, Clone and Accumulator.new it yields canonical initial zero weights. Actual BatchedWeights.new/zip then establishes the raw bounds, canonical projection and zero counter without child-success premises.

Focused accepted results and exact axioms are in RHO-RESUME-CANONICAL.json and RHO-INITIALIZATION-CANONICAL.json. The resume result inherits the existing opaque Formatter Type, not a propositional axiom. All other audited declarations use at most propext, Classical.choice and Quot.sound.

Candidate completion remains open: whole transaction composition, source allocation budget and transaction observables. No production Rust changed and no CU/build rerun was needed.
