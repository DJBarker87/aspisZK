# R19 adopted ELF syscall-link audit

Status: read-only link evidence for the adopted verifier and Pool ELF. This is not a runtime trace proof, a compute-budget/deployment attestation, or an R19 closure. No ELF or other binary is copied into this packet.

Adoption source revision: `c8ea8dd49c81ab970b9dbee8d8b47718f9beb005` on `codex/r1-format-adopt-20261019`; underlying source revision recorded by adoption pins: `9a71031d3a95f838ac6d75bd5c58eeafeb62a9e1`.

Pinned source facts:

- `programs/r1-cost-probe/src/lib.rs`, SHA-256 `806264e5de0b54762872f72f129afad7c1ee5b71333c1a3375955dd8d6080172`: the production `SolanaDigest` implementation delegates `Digest32.digest(parts)` to `hashv(parts).to_bytes()` and passes that backend to `verifier::tx1`/`tx2`.
- `crates/aspis-core/src/digest.rs`, SHA-256 `e9a3476d8d3f05639253ea663aebaade2318af60e2ea0fd87a280e058208aba0`: generic `Digest32` plus host `LegacyHashFn`; that generic host backend is not an additional production program instantiation.
- `programs/r1-cost-probe/src/r1_pool_adapter.rs`, SHA-256 `ae597acf7bb2e3b5a92b45664aabe2f6d2743c6d62b7974c4fc427f332052b7b`, and `src/pool_route.rs`, SHA-256 `43cfa25ec59e5349773599924d318a4b8fda923c4958760fcf1482d8fb2db9f0`: Pool route and adapter call `hashv`, PDA derivation APIs, and the verifier CPI path.

ELF facts, independently hash-verified against the existing adoption packet:

- Verifier `aspis_r1_cost_probe_program.so`, SHA-256 `8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`: `R_BPF_64_32` relocation at text offset `0x23c58` names `sol_create_program_address` (dynamic symbol index 8); relocation at `0x23d90` names `sol_sha256` (index 9).
- Pool `aspis_pool.so`, SHA-256 `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`: `R_BPF_64_32` at `0x65a20` names `sol_try_find_program_address` (index 12); at `0x65ba8`, `sol_create_program_address` (index 13); at `0x65ce0`, `sol_sha256` (index 14).
- Disassembly at all five offsets is the unresolved `call -1` form paired with the relocation. The pinned SBPF loader (solana-sbpf 0.21.1, Cargo.lock checksum `d777d7a89267dd133e985113c7e7f820fb7cfd9123a4a350cf8b39ebae1920bc`) documents R_BPF_64_32 as a call relocation and resolves undefined symbols by hashing their names into the call immediate. Its `hash_symbol_name` uses Murmur3; derived IDs are `sol_sha256=0x11f49d86`, `sol_create_program_address=0x9377323c`, `sol_try_find_program_address=0x48504a38`. The shipped ELF keeps `-1` plus the symbol relocation; those numeric IDs are loader-derived, not literal immediates in this file.
- The two ELF dynamic symbol tables have SHA-256 and the listed PDA syscalls. They do not import Poseidon, Keccak, or Blake3 syscalls. This alone does not rule out a software digest implementation or establish runtime reachability/counts.

The adopted measurement-runtime source pins in `lean-candidates/runtime-meter-query-bound-20261019/runtime-source-pins/pins.json` are for Solana 4.2.1 and expressly do not attest the deployed runtime/version/configuration.

The unresolved R19 premises remain exactly at the generic theorem interface: (1) a successful-runtime-prefix refinement into affordable events each satisfying the 85-unit-per-digest-start inequality; (2) a matching/injection from counted query digests to distinct paid starts; and (3) actual per-transaction initial budget at most 1,400,000 and exactly the two transaction boundaries being summed. The relocations establish symbol-to-callsite linkage only. They do not discharge those execution, metering, or deployment premises.

Raw command/output evidence: `evidence/elf-relocations-disassembly.txt`. It records the LLVM objdump binary hash/version, ELF hashes, relocation rows and disassembly windows. No build or replay was performed.

Tool/loader provenance: `llvm-objdump` was `/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objdump`, SHA-256 `fc4f5e9e22e43c299297db54df0bf2ef0d0d5604b5429ffd6eeeb21d821c733e`, LLVM `20.1.7-rust-dev`. The adoption Cargo.lock pins `solana-sbpf 0.21.1` with checksum `d777d7a89267dd133e985113c7e7f820fb7cfd9123a4a350cf8b39ebae1920bc`; its `elf.rs` SHA-256 is `02198fa599ad39030e01ace964a171e72ccb618100ae7f2e704e3e19fdcb166e` and `ebpf.rs` SHA-256 is `53e2cce4ae04bc7be99740dd86b6cc0d88a4e6049a976d2129647d0a76bc6e46`. `evidence/undefined-syscalls.txt` records the complete undefined-symbol names and relocation counts for both pinned files.
