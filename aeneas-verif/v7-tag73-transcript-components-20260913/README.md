# V7 Tag-73 transcript component source extraction

This bundle records three independently translated, production-core V7
transcript components from `main` commit `c627b68d27c105937b99ea9c508c46688988861b`:

| Component | Production function | LLBC SHA-256 |
|---|---|---|
| Point claims | `decode_and_absorb_point_claims` | `4b7144bd05676cdbf7f909035ed2e9e5ac483b83699901dcf170b0d35fbdd39b` |
| Semantic sumcheck | `verify_compact_semantic_sumcheck` | `1b300dd0290f32bb3071f5375b79b59215d7b8e9264dc9dc019d20a9ebc90a7f` |
| Final vector | `decode_and_absorb_final256` | `af704accc99ba6616690acc5ce0eadfeddd128c2279d14bc0aee290a98d1572e` |

All three were extracted with Charon `0.1.223` using its `aeneas` preset,
built MIR, default sysroot, and a dedicated task-owned target directory. They
were translated with the pinned `aeneas-d860-v6-linux` binary using the Lean
backend, split files, JSON output, implementation namespace, and
`-loops-no-rec`. `SHA256SUMS` covers every committed generated output.

The components retain their real generic fixed-field stream interfaces and
fail-closed `Result` returns. This bundle is component source evidence only;
it does not claim that the complete verifier callback/control-flow composition
has been bridged. That composition remains the next source-bridge obligation.

Representative replay shape (with task-local paths substituted):

```sh
charon cargo --preset aeneas --mir built --sysroot default \
  --start-from crate::v6_transcript::decode_and_absorb_point_claims \
  --dest-file V6PointClaims.llbc -- \
  --locked --package aspis-core --lib --features aeneas-observer
aeneas -backend lean -namespace V6PointClaims -dest generated-pointclaims \
  -split-files -emit-json -impl-namespace -loops-no-rec V6PointClaims.llbc
```

The semantic-sumcheck and final256 replays are identical except for the
selected source function and output names.
