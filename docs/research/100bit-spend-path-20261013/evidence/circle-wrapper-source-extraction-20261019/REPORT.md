# Actual R1 circle wrapper extraction attempt

The exact wrapper body from `crates/aspis-r1-cost-probe/src/sampler.rs` was isolated with three opaque callees. Production source is unchanged. Charon succeeds; Aeneas fails in `InterpReduceCollapse.collapse_ctx_following_sequence` (`Not_found`) while joining switch branches. No generated Lean or wrapper-refinement theorem is claimed. The next step is to isolate the toolchain join failure or prove an explicitly identified source migration equivalent, then instantiate the existing callee proofs.

Both phases ran natively on the NUC in separate scopes with MemoryHigh=6 GiB, MemoryMax=8 GiB, MemorySwapMax=0. Charon: exit 0, 0.201 s, maximum process RSS 136168 KiB, zero swap. Aeneas: exit 2, 0.401 s, maximum process RSS 61424 KiB, zero swap. Exact source revision, tool pins, commands, outputs and logs are preserved. Axioms auditing does not apply: extraction failed before Lean generation.

The first admission controller rejected the launch before any job started: it summed ancestor slice current memory (including descendant usage and retained file/slab cache) alongside reservations. The successor gate counts non-overlapping active unbounded execution scopes and leaf services, all finite reservations (including Docker), an 8 GiB candidate, an 8 GiB OS reserve, and independently requires at least 14 GiB MemAvailable. Both fresh per-phase gates passed with 32.375 GiB finite reservations and approximately 6.389 GiB unbounded execution usage. Both controller versions and all inventories are retained; this is an explicit accounting correction, not a claim that the first gate passed.

This packet is component evidence, not a complete verifier or 100-bit soundness release.
