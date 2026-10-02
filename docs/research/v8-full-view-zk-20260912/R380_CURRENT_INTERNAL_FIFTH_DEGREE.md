# R380 current internal fifth-power degree status

The generic polynomial lemmas in `AspisV8R19.R380InternalFifthDegree` are promoted and compile in the saved focused runs. They bound a conditional internal fifth-power layer followed by a linear layer, and two such layers from degree-one inputs/constants. The evidence bundle records both the root-relative and module-qualified cache runs; the latter was needed because the qualified olean artifact was missing. Its portable checker validates the complete saved evidence without recompilation.

The next proposition is the selected-source binding for `internal_round`: establish that its active lane 0, linear layer, and constants are represented by the generic polynomial model. Packing occurs downstream, after `interpolated_internal_pair`; it is not part of the `internal_round` helper. After that binding, the full projected terminal degree proof remains. This note does not claim Rust-to-polynomial correspondence or close the terminal degree obligation.

Evidence and source hashes are in [the R380 evidence bundle](evidence/r380-internal-fifth-degree/README.md).
