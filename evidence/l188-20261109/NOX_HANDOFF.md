# NOX_ handoff — L188 source-to-ELF reproduction and audit (gate row 9)

Branch codex/cx-l188-20261109, merged from research at a46dd8cc2a4. No push.
Host workspace: /home/dombarker/project-offloads/codex-cx-l188-20261109.
**Target not yet established.**

## Claim established

Both release verifier ELFs are reproduced byte-identically from the frozen
source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Each build started from a cold
private Cargo target directory, used the existing Solana 3.1.13 / platform-tools
v1.52 install, and ran offline and locked.

- Default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` (NOX_B002).
- Devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` (NOX_B003).
  This equals the ProgramData bytes NDZ read back for devnet program
  CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ (authority none). The match is
  against NDZ's recorded figure; NOX made no new on-chain read.

These are the first reproductions without a warm seeded cache or the S10
diagnostics wrapper. NCR and NCY copied Low2's warm target and used the
wrapper.

**Correction to the brief.** The FJd receipts are not how the pins were built.
FJd_SBF_default and FJd_SBF_devnet FAILED their pin gates, producing ff089599…
and 8f695160… (FJd_ELF_GATE.md). The pins come from the s10-repin3 recipe,
which NCR and NCY reproduced. NOX_B001 ran the FJd recipe exactly on the frozen
export and got ff089599… again. NOX_B002 differs from B001 in one variable,
`CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3`, which B002 drops; it
matches the pin.

The mechanism is that the override changes every crate's `-C metadata` hash.
That changes the symbol hashes, and with them the code layout in
`verifier::resume`, the `Reader::raw` instances and `entrypoint`: 245 bytes of
.text and 4 bytes of .rel.dyn, with an identical section table. The FJd gate
failure is therefore explained, and the frozen release is not implicated.

## Profile and semantics facts (T2)

The table covers aspis-core, aspis-statement, aspis-r1-cost-probe and
aspis-r1-cost-probe-program. Every row comes from the actual `cargo -v` rustc
lines in host/analysis/profile/rustc_cmds_NOX_B002.txt.

| Setting | Value |
|---|---|
| opt-level | 3 |
| overflow-checks | absent, so off. `rustc --print cfg -C opt-level=3` has no `overflow_checks`. |
| debug-assertions | off |
| panic | abort (target spec `panic-strategy: abort`). `custom_panic` is exported. |
| lto | none (cargo default; no `-C lto`) |
| codegen-units | default (16; no `-C codegen-units`) |
| debuginfo | stripped (`-C strip=debuginfo`) |
| other flags | `-C embed-bitcode=no`, `-Zremap-cwd-prefix=`, `-C link-arg=--threads=4` |
| target | `sbpf-solana-solana`, features `+store-imm,+jmp-ext` |
| Cargo profile settings | The workspace has no `[profile.release]`. Overflow checks are on only for aspis-r1-cert-check and aspis-r1-cert-build, which are not linked into this ELF. There is no `.cargo/config` build setting; the file holds only an xtask alias. |

The features per crate are:

- aspis_core: `r0`.
- aspis_statement: `r0`, `pool-v1-kernel` and the 12 `pool-v1-pair-forest-*-audit` kernels selected by `optimized-terminal`.
- aspis_r1_cost_probe: `default`, `optimized-terminal`, `private-leaf-salts`, `program-build`.
- program: `custom-heap`, `default`, `pool-adapter`, `private-leaf-salts`.

**Arithmetic semantics of the deployed code.** Integer `+`, `-` and `*` wrap,
and shift amounts are masked. Explicit `checked_*` calls remain checked. Slice
indexing, division by zero and `unwrap` still abort. This is the input the R22
row needs.

**R22-dependent set.** This comes from NOX_R22_CONFIG.json, which applies a
stated rule to Stream C's PCUE_EQ_STATUS.json. 24 gate modules contain a
function definition proved equal to an overflow-checks-ON emission, so they
carry checked semantics. That does not match the deployed profile.

- AspisC2HostEmbedding.Funs, AspisR1CurrentWide.Funs, AspisR1EbyKFinish.Funs
- AspisR1Post25Sampler.Funs, AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
- AspisR1PrefixAggregateParser.Funs, AspisR1Qm31SamplerIndex.Funs, AspisR1SemanticCallExtraction.Funs
- AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions, AspisR1WideToBytesSource.Funs
- AspisR1WithdrawalCaller.Funs, AspisR72Sampler.Funs
- AspisV8R19.{Complex,Guarded,Quartic}FieldSlice
- CurrentCompactCallerModelV1, NFG_CheckedFieldRef.Funs, NMT_first.Funs, NMT_tx1.Funs
- R1CandidateFieldParsers, RPz7_FIo_NativeFuns (MIXED), RPz7_FIp_DotDecode
- S1NativeCompactModelV1, SelectedWideViewFunsV1

Two modules use wrapping gate models, as the CONFIG_MISMATCH definitions show:

- NMT_stage1_owned.Funs (`stage1_owned`, Usize.wrapping_add)
- RPz7_FIo_NativeFuns (`canonical.reduce`, `Dot.finish`, `EbyKDot.push/finish`, `Variant.row/row_loop`)

71 modules are UNDETERMINED: they have no overflow-on comparison
(NO_FRESH_EMISSION, FAILED or GATE_SOURCE_UNAVAILABLE), and the gate source
text itself was not inspected for this. The list is per module and
conservative. A checked definition with no arithmetic, such as `is_zero`, puts
its module on the list without creating a real R22 obligation.

## ELF audit (T3)

The figures below are for the default ELF; devnet is identical apart from the
two .rodata ID slots.

| Item | Default ELF |
|---|---|
| File | ELF DYN, 4 program headers |
| Entry | 0x51ca8 = `entrypoint` (552 bytes). `process_r1_cost_probe_instruction` has no symbol, so it is inlined. |
| Sections | .text 1,526,352 · .rodata 20,704 · .data.rel.ro 4,904 · .dynamic 176 · .dynsym 312 · .dynstr 168 · .rel.dyn 10,176 |
| Exports | `entrypoint`, `custom_panic` |
| Imports | `abort`, `sol_create_program_address`, `sol_get_clock_sysvar`, `sol_log_`, `sol_memcmp_`, `sol_memcpy_`, `sol_memmove_`, `sol_memset_`, `sol_set_return_data`, `sol_sha256` |
| Not imported | `sol_alloc_free_` (in-program BumpAllocator, 256 KiB at HEAP_START_ADDRESS), `sol_invoke*` (the verifier makes no CPI), `sol_get_return_data` |
| Read-only data | The ID slots are at file offsets 1,526,640 (Pool) and 1,526,672 (registry) |
| Stack | 34 compiler stack-offset diagnostics. All 34 symbols are absent from the linked .symtab and the relocations (freeze method; name-level only). |
| Linked unstripped ELF | 1,619,912 bytes, sha256 2690f0b1…94aa |
| Function symbols | 301 distinct defined function symbols in the linked ELF; host/analysis/NOX_FUNCS_default.json lists them |

The symbol association covers 337 name targets drawn from the frozen and cut
selections in PCO_extract_specs.json and from the brief. 61 have a named
compiled symbol: for example `owned::stage1_owned`, `owned::stage2_owned`,
`owned::stage2`, `authenticate_asq8_accounts`, `validate_asq8`,
`BatchedWeights::finish`, `r0::heap::filled`, `field::qm31_m31_dot`,
`ValidatedRecord::decode_k/payload`, `Weights::scalar_factor`, every
`pool_v1` decode/encode/validate root, the `state_only_poseidon` rounds and the
`r1_pool_adapter` reconstruction functions.

The rest are not individually identifiable. This build has no DWARF and no
inline map, so they are inlined, merged or dead-stripped. The list includes:

- `compact::expand_values`, `candidate::query_values`, `multiproof::verify_in_place`
- `verifier::update_residue_row`, `sampler::add_small_base_p` and `low_base_p_digits`
- `fast_pairing::canonical::reduce`, `Dot::finish`, `EbyKDot::push/finish`
- `transport::Variant::row`, and all M31/CM31/QM31 add/sub/mul/neg/reduce

They plausibly sit inside the large containers:

| Container | Size (bytes) |
|---|---:|
| `verifier::candidate::tx1` | 91,920 |
| `verifier::candidate::tx2_common` | 93,240 |
| `verifier::candidate::batch_merkle` | 16,072 |
| `verifier::resume` | 7,672 |
| `r1_semantic::verify_finish` | 8,424 |
| `weights::Weights::pair` | 131,192 |
| `weights::factored_s2_libra_weights` | 114,752 |
| `compact::expand_semantic` | 1,232 |
| `multiproof::node_count` | 1,480 |

"Plausibly" is not shown. **This association is by symbol name and build
provenance; it is not a semantic proof.**

## Assumptions

None was discharged. The packet adds no assumption and widens none.

The FJd root cause is now established: it was a recipe error, not a source or
toolchain change. The provenance of the release ELFs moves from "inherited pins"
to "reproduced from frozen source". The compiler, LLVM, linker,
cargo-build-sbf, registry, allocator and loader stay trust. NOX_REALIZATION.md
gives each of them a line the inventory can carry.

R22 stays OPEN.

## Validation

Six scopes ran against a budget of 12 build plus 20 ordinary: 3 build (B001 to
B003) and 3 ordinary (O001 to O003). There was no Kani run, no Lean run and no
network operation. Every scope ran under its own `systemd-run --user --scope`
with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and TasksMax=64, wrapped in
`/usr/bin/time -v` and `timeout` (1800 s for build, 180 s for ordinary). The
other-scope count at admission was 0 or 1, disk was at least 62 GB free, and
there were no memory events. NOX_COMPILE.tsv and NOX_ATTEMPTS.jsonl hold the
figures, and host/receipts/<attempt>/ holds the raw files: argv, env, limits,
time.log, stdout/stderr, cgroup peaks and admission log. `#print axioms` is
N/A.

Disclosures:

- NOX_build.sh was edited after B001. The edit added a `fjdwrap` variant that
  was never used. The behaviour of `fjd` and `plain` is unchanged; the script's
  final sha256 is 28de03cc…ad3c.
- cargo-build-sbf wrote a fresh program keypair into each out/ directory. These
  were left on the host at mode 0600, never read, and are not committed.
- No file outside the workspace was written. The pinned host copies (NCR_B003,
  NCY_B001, NDZ) were read for their hashes only.

## Separate observation (Pool, not in this job's scope)

NDZ's devnet Pool program BmsNik… runs ELF 121f3e29…, not the current frozen
Pool e0e49c34… (PCH_). Gate row 14 names e0e49c34. If (aj)(a) puts Pool
execution in the claim, the deployed Pool needs its own association.

## Next

See NOX_REMAINING.md.
