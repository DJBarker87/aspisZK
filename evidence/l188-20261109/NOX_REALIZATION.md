# NOX_ AllocatorABICompilerSourceToELF realization statement (L188, gate row 9)

Job NOX_, 2026-11-09. Branch codex/cx-l188-20261109. Target not yet established.

## What L188 does and does not establish here

This packet establishes that the frozen verifier source, built by the recorded
toolchain and command from a cold private cache, produces byte-identical copies
of both release ELFs. The default pin is f8c0ec72…43d4 and the devnet pin is
63ad3e9c…4299. The devnet ELF is the one whose bytes NDZ read back from the
finalized, authority-less devnet ProgramData. That makes the chain from source
to deployed bytes a reproduced build fact. It is not a trust assumption about
the provenance of the binary.

It does not establish that the compiled code means what the Rust source means.
The rows below keep the compiler, LLVM, linker, platform-tools, loader and
runtime as trust. It does not establish that the gate's Lean bodies describe
the deployed binary's arithmetic. The deployed build wraps on integer overflow,
while most proved gate bodies are checked translations. That is the R22 row,
which stays OPEN (see NOX_R22_CONFIG.json). The symbol association in
host/analysis/NOX_ELF_AUDIT.json is by name and build provenance only, and most
gate leaves are inlined (NOX_HANDOFF.md). No mainnet deployment exists, and the
default ELF is deployed nowhere.

## The chain

| Link | Value | Evidence | Status |
|---|---|---|---|
| Source revision | `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Tree hashes on research HEAD a46dd8cc2a4: crates `9c52e6b9…`, programs/r1-cost-probe `7f2e497c…`, Cargo.lock `8b19d7e9…` (file sha256 `5782e6a3…ba22ef`), root Cargo.toml `bdc6be47…`. All are identical at both revisions. | `git rev-parse <rev>:<path>`; NOX_ATTEMPTS.jsonl | Verified (gate row 14 for these paths). programs/aspis-pool differs, as expected after the legacy removal. |
| Build input set | `git archive` of the frozen revision over Cargo.toml, Cargo.lock, .cargo, crates, programs, xtask, audit/poseidon-pair-probe/program, and docs/research/v8-r0-zk-20261009/{refine/writers,refine/blockwriters,refine/poseidon,z4,c3} (the workspace members and path dependencies). The tar sha256 is `40494a95…10b7`. | NOX_O001 (offline, locked metadata resolves) | Reproduced |
| Toolchain | cargo-build-sbf 3.1.13 (sha256 `46e50d5d…5d6c`); platform-tools v1.52 (anza rust `790f1537…`, cargo `ca74c32f…`, newlib `f0f8003d…`); rustc 1.89.0-dev (sha256 `d95c95b6…6002`); cargo 1.89.0 (`b4171a5b…`); LLVM, clang and LLD 20.1.7 (anza-xyz/llvm-project `78496716…`, ld.lld sha256 `384b5aeb…`); target `sbpf-solana-solana`. | host/analysis/profile/ | Recorded |
| Build command | `cargo-build-sbf --manifest-path programs/r1-cost-probe/Cargo.toml --sbf-out-dir <out> --features pool-adapter,private-leaf-salts --skip-tools-install --offline -j 4 -- --locked` under `env -i` with HOME, USER, `PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin`, `CARGO_HOME=/home/dombarker/.cargo`, a fresh `CARGO_TARGET_DIR`, `CARGO_NET_OFFLINE=true` and `CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4`. Devnet adds `ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs` and `ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`. NOX passed `-v` to cargo to log the rustc command lines; it changes logging only. `CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL` must NOT be set (see below). | host/out/NOX_B00{2,3}/env_exact.txt, cmd.txt | Reproduced |
| Default ELF | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, 1,563,728 bytes | NOX_B002 | BYTE-IDENTICAL to the release pin and to the NCR_B003 host copy |
| Devnet ELF | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, 1,563,728 bytes | NOX_B003 | BYTE-IDENTICAL to the release pin, to the NCY_B001 host copy and to the NDZ copy |
| Default vs devnet | 63 differing bytes, all in .rodata at file offsets 1,526,640 to 1,526,703: the Pool ID slot at 1,526,640 and the registry ID slot at 1,526,672. Section tables are equal. | NOX_ELF_AUDIT.json `diff_B002_default_vs_B003_devnet` | Agrees with freeze-20261020 and NDZ_ELF_SCAN |
| Deployed program | Devnet program `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`, ProgramData `7GVKbnPt1XkYvnZURDLRKJqC89qbgfqP912hM3aUojRk`, upgrade authority none, 1,563,728 bytes, sha256 63ad3e9c…4299. The association was read at finalized slot 516454111. | evidence/devnet-rehearse-20261029/NDZ_DEVNET_RESULT.md (lead-executed, 2026-10-29) | Reused, not re-read on chain by NOX (0 network operations) |
| Default deployment | none | — | No deployed instance. Mainnet is not deployed. |

### Cause of the FJd mismatch (resolved)

FJd_SBF_default produced `ff089599…` and failed its gate, with the cause left
open. NOX_B001 ran the FJd recipe exactly, on the frozen export, from a cold
cache, and reproduced `ff089599…` again. The FJd corpus was therefore not the
cause. NOX_B002 changed one variable: it removed
`CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3`. That build gives
`f8c0ec72…`.

The override changes the profile of build-script and proc-macro units. Cargo
folds those units into the `-C metadata` hash of every dependent crate, for
example `aspis_core.b7806d14…` against `aspis_core.b775d6a5…`. The changed
hashes alter the mangled-symbol hashes, which change code layout in one region.
The section table is identical. 245 bytes of .text differ, inside
`aspis_r1_cost_probe::verifier::resume` (7,672 bytes), the
`verifier::Reader::raw` instances, `entrypoint` and two `Rc::drop_slow`
instances, together with 4 bytes of .rel.dyn
(NOX_ELF_AUDIT.json `diff_B001_vs_B002`).

The pins are reproducible only without the override. This is one failure
shape, seen once. It was not repeated.

## Trust lines for the inventory (each retained; none discharged by this packet)

1. **P7-SBF-Compiler.** Platform-tools v1.52 rustc 1.89.0-dev (sha256
   d95c95b6…6002, anza rust 790f1537) translates the frozen Rust source to SBF
   preserving its semantics. That includes integer wrapping in the release
   profile, panic=abort, and slice-bound and division checks. Removal condition:
   none for the tool (a verified compiler would be a different trust base).
2. **P7-LLVM-LLD.** The anza-xyz LLVM, clang and LLD 20.1.7 (78496716) code
   generation and linking for target sbpf-solana-solana (features
   `+store-imm,+jmp-ext`; pre-link `-z notext --Bdynamic -z max-page-size=4096`)
   preserve the semantics of the LLVM IR. Removal condition: none for the tool.
3. **P7-cargo-build-sbf.** cargo-build-sbf 3.1.13 (46e50d5d…5d6c) and cargo
   1.89.0 (ca74c32f) select the recorded flags and post-process (strip) the
   linked ELF into the deployed .so. These steps are reproduced bit-exactly but
   not proved. Removal condition: none for the tool. The reproduction removes
   only provenance doubt.
4. **P7-Registry-Crates.** The crates.io sources in `/home/dombarker/.cargo/registry`
   are the ones the Cargo.lock checksums name, including solana-program 2.3.0,
   the entrypoint, `BumpAllocator` and the syscall stubs. Cargo verifies the
   lock checksums when it unpacks a crate, not on every later build. Removal
   condition: an archived registry snapshot with per-file hashes, or a vendored
   build.
5. **AllocatorABI (BumpAllocator, in-program).** The verifier has no allocator
   syscall: `sol_alloc_free_` is not imported. Its `#[global_allocator]` is
   solana_program's BumpAllocator over `HEAP_START_ADDRESS` with len 256 KiB
   (programs/r1-cost-probe/src/lib.rs:18-19). The trust is that the runtime maps
   a heap region at HEAP_START_ADDRESS of at least the size the transaction
   requested, and that any access outside the mapped region, or any allocation
   failure (null, then the alloc-error handler, then `abort`), terminates the
   instruction with an error and no committed state. Used by: the (bo)
   abortIndicator reading. Removal condition: a proved realization of the
   pinned runtime's heap-region mapping and abort semantics.
6. **SBF-Loader/VM.** The deployed loader (BPF upgradeable loader on devnet,
   Agave 4.4.0-beta.1 at the time of NDZ) loads this ELF with the recorded
   program headers (entry 0x51ca8 = `entrypoint`; LOAD R E .text, LOAD RW
   .rodata + .data.rel.ro, LOAD R dynsym/dynstr/rel.dyn). It performs the
   relocations in .rel.dyn, resolves the ten imports (`abort`,
   `sol_create_program_address`, `sol_get_clock_sysvar`, `sol_log_`,
   `sol_memcmp_`, `sol_memcpy_`, `sol_memmove_`, `sol_memset_`,
   `sol_set_return_data`, `sol_sha256`) to their documented syscalls, and
   executes the SBF semantics, including the 4 KiB stack-frame limit. Removal
   condition: a proved realization of the pinned loader and VM. The existing
   runtime rows (RuntimeSyscall, RuntimeMemcmp, RuntimeReturnData,
   RuntimeClockSlotBinding) cover the individual syscalls.
7. **Stack frames.** The build emits 34 "Stack offset exceeded" diagnostics
   (34 distinct symbols). Under the freeze-20261020 method, every named symbol
   is absent from the linked unstripped .symtab and from the stripped
   relocations. That is a name-level check, not a frame-size proof for the
   functions that survive. The rows stay as in freeze/S10.
8. **CheckedVsWrapping (R22), OPEN.** The deployed profile is opt-level 3 with
   no `-C overflow-checks` and no `-C debug-assertions`. `--print cfg` at
   opt-level 3 lacks `overflow_checks` and `debug_assertions`, and the frozen
   Cargo.toml enables overflow checks only for aspis-r1-cert-check and
   aspis-r1-cert-build, which are not in this ELF. Integer `+ - *` and shifts
   therefore wrap or mask in the deployed code. NOX_R22_CONFIG.json lists the
   24 gate modules with a function body proved equal to an overflow-checks-ON
   emission (checked semantics), of which RPz7_FIo_NativeFuns is MIXED. It also
   lists the 2 modules with a wrapping gate model, and 71 modules whose
   configuration is undetermined. Removal condition: as in
   SOUNDNESS-CLAIM-DRAFT 4.3 (every reached cone TOTAL or caller precondition
   proved), or an owner-retained trust row.

## Reproduction resources

The three build scopes used 37 to 79 s wall, at most 648,332 KiB process RSS
and at most 1.53 GB cgroup peak, with swap 0. They ran at caps 6G/8G with swap
0, 64 tasks and a 1800 s build-class timeout, with no memory events
(NOX_COMPILE.tsv).
