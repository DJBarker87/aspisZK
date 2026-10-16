# Focused R1 row-1 `echeck` extraction

This immutable experiment extracts the exact `verifier.rs::echeck` body from a small isolated Rust crate and specializes it through a separate `echeck_round1` wrapper. It does not extract or prove `View::parse`; the Rust caller's `round1` slice/length relation remains separate.

Pinned source: proof worktree `crates/aspis-r1-cost-probe/src/verifier.rs` SHA-256 `b62d50ad47f9f4c736323f54e6d2b90e80fe18d4730d29994febe0ca0756734d`; exact echeck body SHA-256 `7048dc298b2770e6daad4f46dc16bbb4911e7c2cd87e9784c07b3173e713b3f8`; field sources are preserved byte-for-byte in `source-kit/input/src/` and pinned by `manifest.json`.

All stages exited 0, run sequentially under distinct systemd user scopes with MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0, TasksMax=128, offline Cargo, one Cargo job, and optimized release profile:

- Cargo build: 1.009 s, peak process RSS 140060 KiB, cgroup peak 59514880 bytes.
- Charon built-MIR extraction: 1.175 s, peak process RSS 210796 KiB, cgroup peak 112214016 bytes.
- Aeneas translation: 0.627 s, peak process RSS 110528 KiB, cgroup peak 94109696 bytes.

All three had zero swap and no cgroup memory events. Tool pins: Rust `1.98.0-nightly` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, Cargo 1.94.1, Charon SHA-256 `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`, Aeneas SHA-256 `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.

The generated Lean contains the actual `echeck_round1 → echeck → echeck_loop` definitions. The loop calls generated `Slice.chunks_exact`, `IteratorChunksExact.next`, and the actual generated `WideExact.from_le_bytes`; these three functions are non-opaque. Aeneas emitted one external template, `core.option.Option.ok_or`. A historical Aeneas output already contains the matching `ok_or` model; this model's source/object provenance must be retained if imported. The translation itself is not a Lean proof.

Raw outputs, logs, receipts, runner, scope launches, and the complete reconstructible input kit are stored below this directory. `CanonicalLiteralRow30Chunks.lean` (outside this bundle at `/tmp/CanonicalLiteralRow30Chunks.lean`) is a no-build symbolic lemma draft for the exact seven 32-byte chunks of an arbitrary 224-byte list; it uses a seven-step structural recursion rather than reducing concrete bytes.

`source-kit/option-ok-or-model/` retains the exact Rust core `option.rs` file from the pinned nightly and the prior generated Aeneas Lean file containing the `Option.ok_or` model. That Lean model is an explicit source model matching the Rust `match`; it is not a direct Charon body extraction from this echeck run. Its provenance is recorded separately.
