# Native fidelity remains open

No D188/native fidelity credit is claimed for this Lean continuation. Imported and new source-model results retain the distinction between a checked extracted/model operation and its faithful native association.

The fixture relies on master and checkpoint decoders that fill sequence arrays through iter_mut; the lane decoder fills tree/frontier elements through mutable iteration. Zero sequence cells do not exercise nonzero writes. The real lane/frontier bytes are nonzero. Native op33/34/38/48/49/50 associations remain unsupplied.

Raw terminal-validator composition invokes snapshot/afterstate/frontier encoders and digest encoders with mutable element/range access. The new generic associations identify the two Lean extractions; they do not supply the static scan plus native differential required by narrowed D188. The inherited verifier suffix additionally relies on sampler, weights, pending/query/flush/result stores, with the inherited narrowed boundary. Emission remains the checked return-data model, without native syscall/ELF correspondence.

No Kani/native differential, Rust, SBF or full package replay is claimed. Shipped sources are unchanged, so the ELF rebuild trigger has not fired; the three release hashes remain inherited pins.
