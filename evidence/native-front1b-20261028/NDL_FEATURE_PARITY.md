# Feature and artifact scope

Every verifier helper compile uses default + private-leaf-salts + optimized-terminal + program-build. Per-crate expanded features are present in EVERY graph receipt, including statement r0/pool-v1-kernel and its twelve optimized audit features. The selected targets are library helpers in weights.rs/multiproof.rs, not verifier-program entrypoints; no program-root/no-entrypoint claim is made. The unused aspis-verifier dependency's no-entrypoint feature is recorded in metadata rather than attributed to the tested helper's root.

Standalone core K034–043/K079–080 selects r0, which matches aspis-core's resolved feature set under these deployed verifier library features. Actual qm31_pack_base4 and the CM square-factor source span have no internal feature branch. The complete instrumented files normalize to the exact frozen bytes; only cfg(kani)-only hook/contract lines are removed. Frozen arithmetic bodies were never replaced in shipped files. Native probes and host features are not SBF artifact equivalence evidence.

No shipped-source edit occurred, so default/devnet/Pool ELF rebuilds were not triggered. Their inherited pins are reported as inherited, not newly verified ELF hashes.
