The local source extraction succeeds in `frontier-c-enums-20261015`.
This is generated Lean source, not a Lean compilation or a proof of
`SourceSerializerRefines`. No Rust-to-Lean semantic closure is claimed.

The actual source change is confined to `r0::Public::public_bytes` in
`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`: replace
the two twenty-digest loops with a shared local `frontier` helper containing
twenty ordered calls to the unchanged `fields` helper. Its `&[Digest; 20]`
parameter type checks the width at both call sites. The field checks, byte
order, `?` propagation, and other serializer operations remain unchanged.
`serializer-before.rs`, `serializer-after.rs`, and `serializer-change.patch`
retain the full before/after source, including the added differential tests.

Each attempt contains an independent dependency-free Cargo input copied from
the nineteen exact declaration spans, the manifest and hashes, LLBC, commands,
tool/environment/provenance receipts, logs, and the executed runner snapshot.
The manifest's revision is the pre-edit HEAD, while `source_sha256` records the
actual working source; these are deliberately separate fields. All three
attempts passed the exact-copy check. The successful source is identical to
the second attempt's source. Build targets are excluded from this evidence.
The runner snapshot records its original worktree context; commands and paths
are retained verbatim, rather than presented as a portable build script.

| Attempt | Change | Charon | Aeneas | Sampled peak group RSS |
| --- | --- | --- | --- | --- |
| exact-a | Original source, broad Option/Result includes | 0, 2.50 s | 2, 0.50 s | 245,776 KiB |
| frontier-b | Actual fixed-width helper, same includes | 0, 2.90 s | 2, 17.13 s | 714,800 KiB |
| frontier-c-enums | Same helper, include only Option/Result types | 0, 1.99 s | 0, 13.17 s | 912,128 KiB |

Attempt A rejects nested-loop returns in `PrePasses.ml:658`. Its extracted
`public_bytes` and `fields` declarations exactly equal historical Linux
attempt B, which failed later in fixed-point computation. Attempt B here
passes loop preprocessing, then rejects enum expansion in the std
`FromResidual::from_residual` body at `core/result.rs:2194`. Attempt C narrows
`--include core::option` / `core::result` to `core::option::Option` /
`core::result::Result`. The standard methods are then opaque foreign LLBC
declarations mapped to existing Aeneas builtins; no local declaration is hidden.
The shared kit runner now records these narrower includes.

Local native arm64 tools:

- Charon `external/aeneas/charon-cb50-metadata/bin/charon`, version 0.1.223,
  SHA256 `776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375`.
  Driver SHA256 `cc41d8ca83d7d0b9ae9ff8484e091d74ec91d90e9da0064f7731a0b355c1b806`.
  Source snapshot `d333b4ec4317e6941452b324949f6830fec52455`; 147 selected
  source/config blobs exactly match historical pin
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.
- Aeneas `external/aeneas/aeneas-verif-workspace/aeneas/bin/aeneas`, reports
  `b59d518`, SHA256 `fbb8dac1a9a57e635a762e04b95aeb46dbd2dab2be5ed54fa9e0b1321c1962cf`.
  Source snapshot `220c7ff9cce569dead1e72ef199775b3417493b7` has unchanged
  `src/` relative to `b59d5188c082f704a418c7cb4e52ad69328002d1`.
- Installed rustc 1.98.0-nightly, commit
  `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, nightly-2026-06-01.

These are different binaries from the historical Linux pins. Their binary to
source rebuild correspondence was not independently verified. No tool install,
host access, dependency build, or Lean build was performed for extraction.

The macOS guard sampled process-group RSS every 50 ms and killed at 3.5 GiB,
below the authorized 4 GiB ceiling; this is not a cgroup hard limit. No guard
fired. Per-command swap counts were zero; pre-existing system swap was nonzero
and unchanged within each extraction attempt. Exact wall/RSS/swap receipts are
in `commands.json`.

The successful output has ten types, nine local nonopaque function entries,
one concrete global `P`, and Clone/Copy implementations. `Types.lean` imports
`Aeneas`; `Funs.lean` additionally imports `AspisR1PublicSerializer.Types`.
The exact target is
`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`.
The retained inner `fields_loop` uses Aeneas's `loop`; termination and byte
specification proofs remain open. Generated files contain no new `axiom`,
`opaque`, or `sorry` declaration. Compatibility with the project's Lean 4.32
proof environment remains open; the existing backend cache uses Lean 4.31.

The focused optimized Rust test build stopped before tests on three unrelated
G8 fixture constructors missing `bump` in this older worktree's
`pair_forest_terminal.rs`. Its exit 101, 32.45 s, 646,656 KiB sampled RSS,
and zero swaps are retained. The coordinator has those caller fixes and must
run `public_serializer_tests` after integration. These tests compare both
variants against the previous loop serializer and reject every serialized
field position at `P` and `u32::MAX`; they perform no proof generation.
