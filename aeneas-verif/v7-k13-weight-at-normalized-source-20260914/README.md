# V7 current release `weight_at` source bundle

This bundle extracts the body-bearing production root
`aspis_core::sumcheck::_::weight_at` from the V7 gate-closure source revision.
Unlike the earlier verifier-root extraction, this root is local and its helper
loops and field operations are present as transparent generated definitions.

## Source and tools

- Git base: `7432cdb7b856ac1995fcba8d6d0dac1cd4a1dbfe`, plus the tracked source
  normalization in `crates/aspis-core/src/{field,sumcheck}.rs`.
- Source hashes: `field.rs` `49fb94aa465647a5addedaa803a40506968678d64277cdeb27635db1d9b56794`;
  `sumcheck.rs` `d8485471a77943b68e26096e545f01d2f90a4474169a04a9f5d5c2a580fdc24e`.
- Charon: pinned `0.1.223` executable at the path recorded in
  `evidence/charon-release.log`.
- Aeneas: pinned patched `d860` executable at the path recorded in
  `evidence/aeneas-release.log`.
- Rust extraction profile: `--release --locked --package aspis-core --lib`.
- Lean: `4.32.0`, using the pinned Aeneas library/cache recorded by the kernel
  logs.

The refreshed LLBC SHA-256 is
`63f09a6f446c5781e23b4f4024e1d6792fdd09b1ad7d4251a59d28defa3eeeb9`.
It includes the source-level extraction-only factorization of the log-eight
grouped-binary arithmetic tail; the operation order is unchanged and the
13-case normalization target passes in both debug and release mode.

## Mechanical generated-code repair

The pinned backend emits the source expression `exp >>= 1u32` as
`Std.U64.wrapping_shr exp 1#i32`. The Aeneas library requires a `U32` shift
operand. `generated/V7WeightAtRelease/Funs.raw.lean` is the byte-exact Aeneas
output. `Funs.lean` makes exactly two integration changes:

1. narrows the umbrella `import Aeneas` to the three used library imports;
2. changes that single ill-typed literal from `1#i32` to `1#u32`.

No value, branch, source operation, or proof-facing definition is changed.
`proof/FunsGeneratedRepair.patch` records the complete diff.

## Checked results

`proof/V7WeightAtReleaseProbe.lean` imports and prints the real root.
`proof/V7WeightAtReleaseFieldBridge.lean` proves exact and canonical semantics
for the current generated QM31 add, optimized lazy-u64 multiply, and optimized
square.  The half, tensor, multilinear, and live log-eight grouped-binary
leaves then prove the corresponding current generated source paths.  In
particular, `generated_grouped_log8_corresponds` covers the literal row-group
and mask reads, exact `[1, alpha^3, alpha^2, alpha]` ordering, both halvings,
successful return, canonical output, and exact decoded equation. Their axiom
sets are exactly:

`[propext, Classical.choice, Quot.sound]`.

The refreshed field/half/tensor/multilinear checks and the new grouped-binary
check all exited zero.  The grouped-binary target used peak RSS 2,674,376 KiB
and zero swap; the other refreshed targets remained below 2.70 GiB.  The outer
component work is now also checked:

- `generated_live_multilinear_component_corresponds`,
  `generated_live_tensor_component_corresponds`, and
  `generated_live_grouped_component_corresponds` discharge the current
  generated dispatcher branches;
- `generated_accumulator_loop_corresponds` proves the complete generated
  `weight_at` loop terminates successfully and returns the exact ordered sum;
- `generated_live_six_component_accumulator_corresponds` instantiates that
  loop for the literal post-round-zero Tag-73 shape: three multilinears, one
  deferred grouped-binary component, and two tensors at log length eight.

All of these report exactly `[propext, Classical.choice, Quot.sound]`.  The
remaining G1 work is caller reachability: derive that six-component shape and
all canonical/length premises from the translated `finish_onefold_relation`
construction and first arity-four fold.  The 256-entry observer consumer then
remains G2.
