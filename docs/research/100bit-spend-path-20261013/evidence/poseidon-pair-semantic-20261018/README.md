# Actual internal-pair caller in the WideExact semantic carrier

`PoseidonInternalPairSemantic.source_success` now derives actual internal-pair execution, canonical output, and pointwise equality with the existing R0P interpolated-internal-pair model in concrete `WideExact`. Inputs are the same canonical source states as the checked exact-QM31 caller. The proof reuses that source theorem and the existing concrete `qm31ToWide` algebra map; it adds no successful-execution, output-identity or hypothetical homomorphism premise.

Three new `PoseidonPairMap` lemmas transport leading/full/internal pairs across any field homomorphism. They keep nonlinear rounds opaque and reuse the existing scalar/round/constant/fold naturality lemmas. The concrete internal-pair theorem consumes the internal-pair transport. Leading/full transports do not claim their actual source endpoints are complete.

The maintained `PoseidonMap` source is byte-identical to the earlier accepted NUC `R1PoseidonMap-h` source (SHA 120f34445bece1c624f6094d4b6f32d36e091366faf5c22a26fdeca2a2030a40). Its eleven existing theorem reports are reused, not counted as new. An exact current-name object was absent locally, so one focused check of that unchanged source built the missing artifact against the current pinned import closure. No package-wide or cold dependency build ran. Old accepted identical-source evidence is retained for provenance, without assuming object compatibility merely from source identity.

There are four new standard-only theorem reports. Current-name Map, PairMap and concrete Semantic checks respectively took 29.73, 19.29 and 13.97 seconds; peak RSS was 2,825,551,872, 2,853,797,888 and 3,413,508,096 bytes; each process swap count was zero. Receipts retain exact revision, compiler, commands, paths, import hashes, aggregate RSS and swap observations.

Rejected PairMap v1 is retained. Simplifying a partially applied map did not rewrite the interpolated constant functions. V2 proves the pointwise constant-function equality explicitly and rewrites it, preserving opaque rounds. No cap was raised or large recurrence normalized.

This is a concrete source/model bridge, not an end-to-end soundness or privacy theorem. Actual canonical input reachability, projected caller composition, remaining external-layer source routines, runtime/artifact correspondence, cryptographic instantiations and privacy obligations remain open. No production Rust or runtime artifact changes in this packet.
