# Focused canonical Merkle checkpoint

Base revision: `a9d4c4bee5e2cf34ac91056b9e9a7a7ab4e1643f`.
Eight selected final targets comprise seven components and one combined
checkpoint. The checkpoint `R1CanonicalMerkleCheckpoint-checkpoint-a` exited
0 in 0.74 s at peak RSS 1,799,100 KiB, zero swap, in the 4G/6G/zero-swap scope.
Its 27 axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No proof-placeholder axiom is present.

All 27 attempts are retained: 19 failed and eight final, with no unchanged
green reruns. Each has a precompile source snapshot, both hash sidecars,
receipt, compiler output, and time log. The C1 recovery result has one benign
unused-simp warning. Successful component and checkpoint audits give
54 report lines in total.

The root checked every attempt's source/sidecars/receipt, resource and time
fields, final current-source matches, all archived object members, and runner
pins. Fourteen central runtime source fingerprints remain unchanged.
`ROOT-VALIDATION.json` records that local evidence audit.

Compiled objects occur only in `objects/canonical-merkle-objects.tar.gz`,
SHA-256 `55990da8864344ff15c0f42733484658309726819e8fbd12a5a90b81ed1158ac`.
`source-manifest.json` gives each source and object hash; `runner/` pins the
Lean environment and capped snapshot runner. `SHA256SUMS` seals the bundle.

This is a focused checkpoint using the compiled cache, not a fresh replay
of the historical release manifest. The theorem premises and remaining
protocol/source/knowledge/privacy work are recorded in
[CANONICAL-MERKLE-RECOVERY.md](../../CANONICAL-MERKLE-RECOVERY.md).
