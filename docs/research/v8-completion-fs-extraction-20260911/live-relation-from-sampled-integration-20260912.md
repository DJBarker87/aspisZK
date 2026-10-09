# Sampled-data live relation integration

`SameBodyLiveRelationFromSampledIntegration.buildFromSampled_success_or_named_rejection`
executes the sampled-data relation constructor on successful chronological
middle and later run records. It produces exactly one of:

- a `Ready` value with the same-body `fromSampled` equality and `Data.Checked`;
- a named `SameBodyLiveRelationFromSampled.Error` rejection.

This retains parser, inverse, opened-pipeline and increment-mismatch failures.
It does not yet compose the preceding successful source/OOD/gamma run, prove
that complete verifier acceptance excludes the rejection alternative, or
supply a random-oracle law.

Focused NUC compile used the pinned Lean 4.32 environment and private union
cache: exit 0, wall 2.68 seconds, peak RSS 6,733,200 KiB, swap 0. Source
SHA-256 was
`9928db7fa0773fa588f0dcd48f637ef0745b096c5979c0a0fca38f5e57c5546c`;
OLean SHA-256 was
`6737560fad988f7a128890c68e71b8f727fbe04dec4de8b250d1e932a04139e1`.
The endpoint prints only `propext`, `Classical.choice` and `Quot.sound`.
Dependency sources were not rebuilt.
