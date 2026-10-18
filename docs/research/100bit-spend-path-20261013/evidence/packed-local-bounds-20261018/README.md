# Actual packed-local scan and canonical input limbs

`PoseidonExternalLocalBoundLoops` proves the actual nested source scan succeeds. The accumulated Bool is discarded by this source; the result deliberately does not assert the Bool is true. The needed arithmetic bounds are derived separately, not inferred from ignored debug-check behavior.

`PoseidonExternalLocalInputLimbsBound` proves the actual extension-limb map equals the named mapped rows, and canonical QM31 inputs imply every resulting raw M31 limb is below P. It reuses the existing source word-vector canonicality theorem. A congrArg under a fixed-size array getter transports the row equality without invalidating dependent index proofs.

The focused NUC scan target passed in1.92s, RSS3,994,972KiB, and the input target in1.66s, RSS3,987,208KiB; both exit0, swaps0, no watchdog abort. Five axiom reports are standard-only. Per-target cgroup limits stayed MemoryHigh4GiB/MemoryMax4608MiB/MemorySwapMax0, with fresh reviewed54GiB reservation and availability gates. Commands, exact sources/import pins, object hashes, time and live watch samples are retained. Raw receipt source_base_revision denotes the pinned NUC workspace baseline; the exact new source hash and integration parent identify these added proofs.

This closes these two leaves only. The raw packed caller, its field decoding, complete packed external layer, remaining evaluator/source correspondence and end-to-end100-bit security/privacy remain open. No production Rust/runtime artifact changed.
