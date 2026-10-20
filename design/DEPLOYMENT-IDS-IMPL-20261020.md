# Deployment ID data slots — 20 October 2026

Implements the Amendment in
`docs/research/100bit-spend-path-20261013/design/LEAD-DECISION-DEPLOYMENT-IDS-20261020.md`.
The previous frozen ELF encoded the IDs in instruction immediates; its
176-byte text obstruction is recorded in `evidence/devnet-r1-20261020/REPORT.md`.
This implementation intentionally establishes a new default artifact.

The Pool and registry IDs are immutable `[u8; 32]` statics in named input
sections `.rodata.aspis_pool_program_id` and
`.rodata.aspis_registry_program_id`. Every use loads through
`*core::hint::black_box(&STATIC)`. Hiding the address prevents LLVM from
propagating the initializer into comparisons or PDA derivation. Runtime
references retain the slots through section garbage collection. Do not add
`#[used]`: this SBF toolchain emits GNU-retain flags and ELF OSABI 3, which
LiteSVM rejects. The retained failed attempt demonstrates that constraint.

The existing compile-time base58 decoder and `option_env!` overrides remain:
`ASPIS_R1_POOL_PROGRAM_ID`, `ASPIS_R1_REGISTRY_PROGRAM_ID`; unset defaults
are `[0x41; 32]` and `[0x44; 32]`. Invalid overrides fail const evaluation.
There is no runtime decoder, new dependency, route, or authority source.
Despite the task description's reference to an env-parameterised build.rs,
revision `30eb0519a` and this base actually implement overrides in
`src/deployment_ids.rs`; no build.rs exists or is needed. Cargo tracks the
`option_env!` inputs. Only `r1_pool_adapter.rs` changes in program source.

The linker merges both input sections into `.rodata`, with Pool at section
byte 0 and registry at byte 32. Same-source default/devnet builds have equal
section tables and `.text`; substituting just those slots reconstructs the
entire devnet ELF exactly. This is an audited property of the pinned
artifacts, to be checked again after compiler, linker, feature or source
changes. It does not assert that arbitrary future builds preserve offsets.

See `evidence/deployment-ids-20261020/REPORT.md` for offsets, pins, standing
gates and fixture CU. The lead's combined stage-2 freeze and any actual
network deployment remain separate work.
