# Exact source-to-ELF obligation: P7 / S10

**Build identity is supported by existing reproductions; semantic preservation remains trusted P7. Native Kani does not execute or verify these ELFs.** A feature-selected host helper proof can contribute only after its caller, profile, target/runtime and abstraction obligations are met. See [differences first](NCR_FEATURE_TABLE.md).

## Statement fixed to the release

Let `S` be the exact frozen source dictionary at `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, `L` the dependency sources and Cargo.lock with SHA256 `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`, `G` the pinned build-script/generated inputs, and `T` the pinned build tools. For each mode `m ∈ {default,devnet,pool}` define `F_m`, `Env_m`, profile and target by the realized [Low2 build manifest](../lowering2-20261026/Low2_build_manifest.json), not by current Cargo defaults or an unexecuted plan.

The **artifact identity obligation** is:

```
ELF_m = Build_T(S, L, G, root_m, F_m, Env_m,
                profile=release, target=sbpf-solana-solana)
SHA256(ELF_m) = pinned_hash_m
LoadedProgramBytes(program_id_m, release_slot/version_m) = ELF_m
```

The first two equations are the reproducible-build association. The third is a distinct deployment/readback association; a rebuild or this document does not attest the current cluster's ProgramData, upgrade authority or runtime feature set. Here “deployed ELF” means the three user/ledger-pinned artifacts, not a fresh claim about a live account.

The **semantic lowering obligation** is separate: for the selected source entrypoints, every admitted runtime execution of the pinned ELF must refine the same feature-selected Rust execution under the recorded ABI, integer semantics and external-call contracts, with the error/acceptance event, relevant state effects and chronological oracle/call observations required by the security theorem preserved. Compiler translation must not introduce an accepted execution outside that source contract. Source/model equality and security-experiment transport remain their own proofs; build hash equality cannot supply them.

Concrete recipe: cargo-build-sbf3.1.13, platform-tools1.52, rustc1.89.0-dev, LLVM20.1.7; optimized release opt-level3, target `sbpf-solana-solana`, locked/offline, j4. Verifier root `programs/r1-cost-probe` uses `pool-adapter,private-leaf-salts` and manifest dependency `optimized-terminal,program-build`; default custom-heap enabled. Pool root `programs/aspis-pool` uses `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` plus its recorded defaults/transitive features. `RUSTFLAGS` is removed; target-specific flags `-C link-arg=--threads=4`. Default removes both deployment-ID variables; devnet sets the exact IDs in NCR_FEATURE_TABLE. Full generated-input/depfile/command pins are in Low2; [NCR_RELEASE_CFG.json](NCR_RELEASE_CFG.json) retains actual selected cfgs/arguments.

Pinned cargo-build-sbf SHA256 `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c`; rustc SHA256 `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002`. Version output reports compiler commit hash/date as unknown: executable hashes, not a guessed upstream commit, identify this tool. This is separate from cargo-kani0.67.0 and Charon/Aeneas tool pins.

## Existing evidence, reused with its qualifications

| Evidence | Exact result / limits |
|---|---|
| [Release ledger](../../design/RELEASE-LEDGER-20261025.md), S10 re-pin3/status evidence | Fixes full three-ELF hashes and historical compiler/source association; ledger alone does not reproduce or certify semantics. |
| [Low2 STAGE2](../lowering2-20261026/STAGE2.md), [build manifest](../lowering2-20261026/Low2_build_manifest.json), per-mode artifact/command/receipt/reservation files | Three successful optimized capped rebuilds, results below. Actual private source revision `8953c28138c7e3bc31a9109e84ab3a9864090057` is evidence-only relative to retained shipped inputs. The inherited capped runner embeds old `b2727...` revision; Low2 explicitly corrects it via actual_build_source_revision. Do not report that stale field as the actual build revision. |
| Fresh local [NCR_RELEASE_INPUT_CHECK.json](NCR_RELEASE_INPUT_CHECK.json) | All132 default,132 devnet and133 Pool repository Rust compiler-input hashes in Low2 equal the frozen4bb3b3f Git bytes;157 unique inputs. This independently confirms the shipped Rust association despite distinct evidence commits. It does not hash an unavailable fresh ELF or recompile. |
| Low2 generated inputs | `circle_tables.rs` SHA256 `7fbe0464c940393bf8c59e676fd60d8411a296f0260f649fa27bbf9447a96491`,6,888,077bytes; explicit generated-input association. It is not an unrecorded source replacement. |
| [Low2 source/certificate/ELF manifest](../lowering2-20261026/Low2_source_to_elf_manifest.json), STAGE1/STAGE3, final_receipt | Existing packet records2,794 exact source references plus14 historical S2W associations through the narrowly checked require_zero S4 bridge;140 selected ordering certificates replayed. These are selected source/ordering checks, not universal machine-code semantic validation or complete native caller closure. |
| sbf-identity `recapture-plan.json` | Records exact recipes and earlier31–33s predecessors, but status explicitly PROPOSED ONLY. Reused as recipe context, never counted as an executed recapture. |

| Reproduced target / full SHA256 | Exit | Wall s | time-v peak RSS KiB | Cgroup memory peak bytes | Swap |
|---|---:|---:|---:|---:|---:|
| default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` | 0 | 26.907 | 685776 | 1329094656 | 0 |
| devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` | 0 | 26.046 | 685980 | 1193914368 | 0 |
| Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 0 | 26.627 | 681900 | 1150156800 | 0 |

Verifier files are1,563,728bytes; Pool605,704bytes. The original scopes used MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64. Their `#print axioms` status is N/A, no Lean compilation. Resource numbers are **historical reused measurements**, not measurements from this audit. time-v child-process RSS and cgroup peak are distinct metrics.

## Fresh reproduction and retained failed attempt

NCR_I001 was admitted (`allowed:true`, exit0) but its inspection payload did not start: this worker passed a stale historical `.../codex-cx-pin-20261020/harness/capped.py` path and Python reported Errno2. The wrapper then reported a missing receipt. This was an **own input error**, corrected under local rule11 using existing system `systemd-run` and `/usr/bin/time`, without repairing shared infrastructure. The earlier stage-3 text saying host work stopped under rule5 is superseded here. Original logs and null unmeasured fields remain in NCR_ATTEMPTS; no failed payload was silently counted as successful.

NCR_I002 then inspected the existing pinned Low2 source/cache in an admitted capped scope, exit0, peak RSS12,144KiB, swap0. Its actual cgroup limits were read back as6G/8G/Swap0/Tasks64. NCR_B003 copied **only the existing compiled target cache** (635MiB), reused the source workspace read-only and ran the pinned default recipe in a private target/out/diagnostic directory. No second source corpus was created and no foreign source/cache was edited. Before and after compilation,156 selected source/configuration hashes matched; pinned compiler and cargo-build-sbf executable hashes matched.

**Fresh default reproduction PASS:** SHA256 `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,1,563,728bytes, build exit0, build wall26.321091037s, full scoped time-v wall27.04s, peak process RSS684,392KiB, cgroup memory peak2,438,955,008bytes, swap0. The compiler log explicitly records optimized release compilation (25.99s), including the selected core/program crates. It reports a jobserver-FD warning and ordinary unused/dead-code warnings; compilation completed and the full artifact hash matched. No tool/configuration change was made to silence warnings.

Exact command, source baseline/workspace revision, before/after hash checks and effective environment are retained in [NCR_B003-stdout.log](NCR_B003-stdout.log), [stderr](NCR_B003-stderr.log), [receipt](NCR_B003-receipt.json), [time](NCR_B003-time.log), reservation/barrier logs and script. Rust baseline is frozen4bb3b3f; reused source workspace revision is8953c28138c7e3bc31a9109e84ab3a9864090057, with byte association checked explicitly, not inferred from commit names. The task script is pinned by hash in the attempts ledger. `#print axioms`: N/A, no Lean.

NCR_I004 collected own compiler-command snapshots and removed only the own copied `NCR_target` cache after the build was terminal. The rebuilt ELF, diagnostics and any generated keypair remain at `/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/`; no key cleanup occurred. The default reproduction is fresh; devnet and Pool remain **historically reused**. No live-cluster readback occurred.

NCR_I005 retained the generated key at mode0600 without reading its contents or changing any funds/authority.

Host budget5/6 scopes conservatively includes the failed pre-payload launch, three successful inspection/retention scopes and one optimized build; Kani0, Lean0. All successful scopes require admission allowed:true AND exit0 and use6G/8G/Swap0/Tasks64, sequentially. No cap increase, memory kill, unchanged solver rerun, compiler bootstrap or full proof manifest replay occurred.

## Precise retained trust rows

| Boundary | Exact trust/obligation | What it does not discharge |
|---|---|---|
| **P7 / S10 compiler semantics** | The exact pinned Rust→LLVM→SBPF platform-tools compiler/linker correctly translates the exact frozen, feature-selected inputs/profile/ABI to each pinned ELF, preserving the source observations needed by the release argument. Reproductions supply artifact identity under this retained trust. | No feature equivalence, host syscall correctness, source/model refinement, heap admission, source-experiment transport, or proof of compiler semantics preservation is obtained from identical hashes. No new compiler axiom is introduced. |
| **Kani tool fidelity / native leaf certificate** | Pinned Kani frontend, MIR/codegen, CBMC/solver and validated replacements correctly establish the specified host-harness property in its domain; honor rule14 quarantine and matched controls. | Does not compile/prove SBPF or certify another selected feature body. Standalone window checks are narrower still. Not collapsed into P7 or Aeneas trust. |
| **D188/P6 Charon–Aeneas / Lean** | Recorded extraction/source-function equalities and accepted Lean kernel/dependency boundaries for selected exact extracted definitions. | Does not establish unextracted callers, arbitrary external contracts or SBF machine-code correspondence. No Lean/axioms audit was run by this worker. |
| **Runtime / SDK / loader** | P2/P3/P4, named SDK/std borrow/allocator/ABI interfaces, CPI/Clock/return-data/syscall contracts, and loaded-program association must hold for the release instance. | Not inferred from a host stub, rebuilt ELF, local value fixture or generic record of desired equalities. |
| **Feature/profile/caller transport** | Bind each certificate to the actual release-selected body/domain, discharge no-overflow/debug-assert differences or prove the necessary simulation, and compose exact caller state/effects. | This is an implementation proof obligation, not an additional cryptographic assumption and not something P7 silently covers. |

Low2's accepted L186 retirement under retained P7 is not reopened merely because Kani uses a host target. This audit identifies the **additional native-to-selected-source joins** that cannot be supplied by L186 retirement. The release-ledger snapshot predates Low2; its historical open-S10 wording must not erase the later artifact packet. Equally, the later artifact packet does not establish every native caller or the deployed100-bit security target. **Target not yet established.**
