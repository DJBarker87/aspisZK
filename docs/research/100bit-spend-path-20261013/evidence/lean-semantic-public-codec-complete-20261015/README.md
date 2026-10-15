# Semantic public codec coverage evidence

This focused Lean target characterizes the image of the canonical bounded semantic public byte model. For canonical `R0P.Public` values whose `nextPairIndex` is below `2^64`, it proves a unique byte representation; it also characterizes parser success and derives the 1455-byte, u32, and initialization-frame bounds. The target reuses `SemanticPublicByteBinding`, `SemanticPublicWireSurjective`, and `PublicInitFrame`.

The failed attempt `semantic-public-codec-complete-a` is preserved: it failed because `FS2.Duplex.State` was not in scope in the initialization-frame statement. Attempt b is the final green source. Its six printed axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

This is a Lean byte-model result. It does not establish correspondence to the Rust public parser, feature-selected transcript parameters, salt derivation, or all source hash-input bounds.

See `source-manifest.json` for exact source/object/runner hashes and attempt metrics. `SHA256SUMS` verifies every file in this bundle.
