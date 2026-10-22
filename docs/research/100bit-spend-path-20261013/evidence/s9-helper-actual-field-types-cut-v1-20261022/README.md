# Actual field-type S9 helper source cut

This packet records the successful attempt7 extraction of the candidate S2
factored helper and projection using the byte-identical `aspis-core` field
types and implementations. `weights::field` and `WideExact::from_le_bytes`
remain transparent. The selected helper and S2 projection are transparent;
the non-S2 `twofold_libra_weights` branch is an explicit opaque boundary.

The four WideExact operations and two QM31 operations are recognized at their
actual Rust source spans and are opaque in this extraction. The source-to-owner
comparison for the four WideExact methods is in
`wide-exact-owner-map.json`. It matches the exact source files and retained
arithmetic owners but leaves the declaration/carrier bridge from attempt7's
opaque calls to those owners open. The parallel task is checking QM31 owner
correspondence. No generated code from this extraction is a checked Lean
proof.

The Aeneas Lean files, including `FunsExternal_Template.lean`, are retained as
diagnostics only; they were not compiled or imported. No production source was
modified. The source-cut adaptation and exact source pins are listed in
`source-identities.json`; `attempt-config.json` pins the tool binaries and the
selectors. Attempts 1–6, including the earlier overbroad Try/from_fn attempts
and the incorrectly matched `twofold_libra_weights` opacity selector, remain
in the candidate workspace as diagnostics and are not part of this accepted
attempt7 packet.

The Charon and Aeneas jobs succeeded under `MemoryHigh=2 GiB`,
`MemoryMax=4 GiB`, and `MemorySwapMax=0`. Their receipts retain the actual
cgroup and admission evidence. `check_packet.py` checks the packet hashes,
source identities, method spans and opacity, cgroup receipts, and exclusion of
compiled objects and Python caches.
