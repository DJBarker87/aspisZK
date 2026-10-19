# Exact finite-word M31 retry probability law

The previous fixed-retry fiber counts now give the exact rational law for the same executable sixteen-slot mask/reject decoder. `retryMass` is the cardinality of an output event divided by the finite uniform input-space cardinality. The no-output mass is exactly 1/2^496. Each accepted residue has mass (1-1/2^496)/P31, using the no-output power identity together with `retryMass_some`. Thus the successful value is uniform conditional on success.

The source organization keeps Nat.card-to-Fintype conversion, accepted-fiber symmetry, the constant finite sum, and rational algebra in separate focused leaves. The finite sum is reduced with named cardinality/sum theorems; it does not enumerate Fin P31. The power identity is proved symbolically before the rational calculation. The final rational leaf passed in 1.37 seconds at 1.54 GB process peak RSS with zero process swap; all four new leaves have standard-only printed axiom reports.

Exact sources, direct imports, compiler commands, base revisions, statuses, timings, RSS, swap and object hashes are retained. The previous count packet supplies the other dependencies and already records the failed broad-Fintype mass proof and its import-only isolation. No full replay or unchanged regression was run.

Remaining: Boolean-bit-to-word law, independent eight-limb packing through the existing WideExact equivalence, whole field-pair/tape law and global exhaustion bound, caller/runtime sampler correspondence, full extractor costs, protocol/source/ROM soundness, privacy and release gates. This uniform-word model law does not itself prove the complete 100-bit spend statement.
