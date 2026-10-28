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

## Fresh reproduction attempt and stop

The historical recipe was quick enough to consider reuse. This worker first requested one read-only capped host inspection to check the pinned workspace/cache and SDK inputs before any rebuild. NCR_I001 admission returned `allowed:true` with exit0, bounded reservation8GiB. The scope then failed **before the inspection payload**:

```
/usr/bin/python3: can't open file '/home/dombarker/project-offloads/codex-cx-pin-20261020/harness/capped.py': [Errno 2] No such file or directory
```

[NCR_I001-launch.log](NCR_I001-launch.log), reservation and barrier log preserve the error. The local wrapper raised `AssertionError: missing submitted receipt`; this is not a missing successful build receipt. The chosen shared historical runner path was absent; local-lean rule5 prohibits repairing launcher infrastructure and requires stop/report. No further host action or unchanged resubmission occurred. No source/cache copy, optimized compilation, Kani or Lean payload started. **No fresh ELF reproduction is claimed.** Scope wall/RSS/swap/inner status were not produced; those fields remain null in [NCR_ATTEMPTS.jsonl](NCR_ATTEMPTS.jsonl), not fabricated from an older receipt. A failed launch consumes1/6 available host scopes conservatively;5 remain unused. No infrastructure change was made.

## Precise retained trust rows

| Boundary | Exact trust/obligation | What it does not discharge |
|---|---|---|
| **P7 / S10 compiler semantics** | The exact pinned Rust→LLVM→SBPF platform-tools compiler/linker correctly translates the exact frozen, feature-selected inputs/profile/ABI to each pinned ELF, preserving the source observations needed by the release argument. Reproductions supply artifact identity under this retained trust. | No feature equivalence, host syscall correctness, source/model refinement, heap admission, source-experiment transport, or proof of compiler semantics preservation is obtained from identical hashes. No new compiler axiom is introduced. |
| **Kani tool fidelity / native leaf certificate** | Pinned Kani frontend, MIR/codegen, CBMC/solver and validated replacements correctly establish the specified host-harness property in its domain; honor rule14 quarantine and matched controls. | Does not compile/prove SBPF or certify another selected feature body. Standalone window checks are narrower still. Not collapsed into P7 or Aeneas trust. |
| **D188/P6 Charon–Aeneas / Lean** | Recorded extraction/source-function equalities and accepted Lean kernel/dependency boundaries for selected exact extracted definitions. | Does not establish unextracted callers, arbitrary external contracts or SBF machine-code correspondence. No Lean/axioms audit was run by this worker. |
| **Runtime / SDK / loader** | P2/P3/P4, named SDK/std borrow/allocator/ABI interfaces, CPI/Clock/return-data/syscall contracts, and loaded-program association must hold for the release instance. | Not inferred from a host stub, rebuilt ELF, local value fixture or generic record of desired equalities. |
| **Feature/profile/caller transport** | Bind each certificate to the actual release-selected body/domain, discharge no-overflow/debug-assert differences or prove the necessary simulation, and compose exact caller state/effects. | This is an implementation proof obligation, not an additional cryptographic assumption and not something P7 silently covers. |

Low2's accepted L186 retirement under retained P7 is not reopened merely because Kani uses a host target. This audit identifies the **additional native-to-selected-source joins** that cannot be supplied by L186 retirement. The release-ledger snapshot predates Low2; its historical open-S10 wording must not erase the later artifact packet. Equally, the later artifact packet does not establish every native caller or the deployed100-bit security target. **Target not yet established.**
