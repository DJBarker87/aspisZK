# V7 current release `weight_at` source bundle

This bundle extracts the body-bearing production root
`aspis_core::sumcheck::_::weight_at` from the V7 gate-closure source revision.
Unlike the earlier verifier-root extraction, this root is local and its helper
loops and field operations are present as transparent generated definitions.

## Source and tools

- Git base: `7432cdb7b856ac1995fcba8d6d0dac1cd4a1dbfe`, plus the tracked source
  normalization in `crates/aspis-core/src/{field,sumcheck}.rs`.
- Source hashes: `field.rs` `49fb94aa465647a5addedaa803a40506968678d64277cdeb27635db1d9b56794`;
  `sumcheck.rs` `a5c753676817fa01a27f2124c03e751619edac27aca93c29b6918be093df6fa2`.
- Charon: pinned `0.1.223` executable at the path recorded in
  `evidence/charon-release.log`.
- Aeneas: pinned patched `d860` executable at the path recorded in
  `evidence/aeneas-release.log`.
- Rust extraction profile: `--release --locked --package aspis-core --lib`.
- Lean: `4.32.0`, using the pinned Aeneas library/cache recorded by the kernel
  logs.

The LLBC SHA-256 is
`be2043d87634da05c6933362d2c54d6fb71e3ee74fa3485ea0992d94136cbc51`.

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
square. Their axiom sets are exactly:

`[propext, Classical.choice, Quot.sound]`.

The final field-bridge check exited zero with peak RSS 2,738,952 KiB and zero
swap under `MemoryHigh=5G`, `MemoryMax=6G`, `MemorySwapMax=0`. This closes the
field-operation subgate only. The live accumulator loop/caller refinement and
the 256-entry observer consumer remain subsequent G1/G2 work.
