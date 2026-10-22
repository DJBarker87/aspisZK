# S9 actual WideExact.add source cut (attempt 5)

This packet preserves the no-override attempt-5 extraction of the candidate helper's actual Rust `field::wide_exact::WideExact::add` body and the reachable actual `QM31::add`, `CM31::add`, and `M31::add` bodies. The cut uses the actual `aspis-core` field and `wide_exact` source files and the candidate `weights.rs` snapshot. It does not replace those types with a synthetic field type or provide a Rust-to-Lean arithmetic refinement theorem.

The pinned extractor input, tool commands, source identities, toolchain/tool hashes, capped resource receipts, and generated Aeneas `Types.lean`/`Funs.lean` are under `attempt5/`. The LLBC itself is omitted; its SHA256 is retained in the Aeneas receipt. No compiled Lean objects or bytecode are included.

The target `WideExact.add` body hash is `711892452ab80cd1a37abcdd41e42375b86d82b577586567da82c5eacadf0f4f`. Its five opaque reachable arithmetic bodies are separately pinned in `metadata/source-identities.json`: `QM31.mul`, `QM31.square`, `WideExact.mul`, `WideExact.mul_m31`, and `WideExact.mul_qm31`. The sixth opaque item is the unrelated free function `twofold_libra_weights`; it is retained as opaque because the cut is S2 helper focused. The extracted selected add call chain itself is visible and transparent.

## Arithmetic profile boundary

The extraction is the candidate source with no local forced overflow-check override in the recorded command environment. The candidate Cargo manifest applies `overflow-checks = true` only to the `aspis-r1-cert-check` and `aspis-r1-cert-build` package overrides, not to `aspis-core`. The release `cargo-build-sbf` invocation/toolchain's effective rustc overflow setting is not captured here. Therefore the production MIR interpretation of `M31.add` is **inferred, not proven**, from the no-override profile; this packet makes no MIR or ELF semantic claim.

The accepted arithmetic bridge should use canonical-input guarded equivalence. For M31 inputs below `P`, the sum is at most `2P-2 < 2^32`, so wrapping U32 addition and checked U32 addition produce the same word. The subsequent conditional subtraction is safe on that range. This supports a guarded Result correspondence without claiming unrestricted equivalence for noncanonical inputs or relying on an unverified production overflow setting.

Attempt 6, which forced overflow checks on, is a separate diagnostic and is not included or treated as production evidence. The Rust source was not modified.
