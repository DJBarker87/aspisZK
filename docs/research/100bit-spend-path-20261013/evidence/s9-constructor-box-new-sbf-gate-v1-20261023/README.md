# S9 constructor Box::new SBF stack gate

This packet records one optimized, capped SBF build of the isolated `Weights::new` candidate. The build command exited 0 and emitted an ELF, but the stack gate **failed**: candidate `Weights::new` has a 4,672-byte estimated frame and reaches stack offset 4,600, 504 bytes over the 4,096-byte SBF frame limit. Other pre-existing functions in the same program also report stack-limit errors; the candidate-specific diagnostic is separately recorded.

The candidate preserves the factor/point calculations but constructs initialized locals before `Box::new`. It changes allocation failure from a returned `Error::Allocation` to allocator abort, so this result is only a successful-run candidate evaluation; it makes no production-equivalence or adoption claim.

The source base is tracked revision `e668ce58d31bde2fe25d8c6e76eba2262fad9e96`; `weights.base.rs` and `weights.candidate.rs` are pinned in this packet. The gate used Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52 / SBPF rustc 1.89.0 with an isolated copy of the warm target cache. The actual scope was verified at `MemoryHigh=3 GiB`, `MemoryMax=4 GiB`, `MemorySwapMax=0`. The copied ELF is intentionally omitted.

Run `python3 check_packet.py` to verify hashes and enforce the non-passing classification.
