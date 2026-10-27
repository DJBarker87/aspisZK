# Historical pin recipe and availability

Stage 1, 2026-10-27. Artifact investigation only; no Lean/Kani or shipped edits.

S10 re-pin3 compiler source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Successful L186 replay source: `8953c28138c7e3bc31a9109e84ab3a9864090057`
(evidence-only; shipped bytes equal `9e23364d3563`). References:
`docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/`
and `evidence/lowering2-20261026/{STAGE2.md,Low2_build_manifest.json}`.
Raw historical capped receipts hard-code b2727acd; the manifests explicitly correct
that label. It is not the compiler-input revision.

The successful recipe is **native Linux**, not Docker. Image tag/digest: N/A;
no image is named by either successful build receipt. Do not invent an image pin.
Agave cargo-build-sbf 3.1.13, platform-tools v1.52, Rust 1.89.0-dev,
LLVM 20.1.7. Host availability and hashes are in `ELa_host_inventory.json`:

- cargo-build-sbf: `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c`
- rustc: `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002`
- diagnostic wrapper: `fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84`

Executable: `/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf`.
Rust: `/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc`.
All three present and hash-identical to L186. No version difference observed.

For each mode, use `--manifest-path SOURCE/programs/PROGRAM/Cargo.toml
--sbf-out-dir OUTPUT --features FEATURES --skip-tools-install --offline -j 4 -- --locked`.
Default/devnet PROGRAM=r1-cost-probe, FEATURES=pool-adapter,private-leaf-salts.
Pool PROGRAM=aspis-pool,
FEATURES=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit.
Default features remain enabled as in the original command.

Environment: PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin;
CARGO_HOME=/home/dombarker/.cargo; CARGO_NET_OFFLINE=true;
CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4';
CARGO_TARGET_DIR=private target; RUSTC_WRAPPER=the hash-pinned wrapper;
S10_DIAGNOSTICS=per-mode private output. Unset RUSTFLAGS and both ASPIS program
IDs except devnet, which sets ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs
and ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q.
The historical recipe does not set CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL;
finish-pair2 adds value 3. Release SBF target compilation is optimized.

Original `/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023`
(including src and wrapper) is absent. Git retains its selected source manifest,
source revision, wrapper and recipe; caches are rebuildable, not git artifacts.
No recorded container image restores that workspace. The successful L186
`/home/dombarker/project-offloads/codex-cx-lowering2-20261026/src` survives:
all 1,243 source census hashes match. Its wrapper/caches also survive.
Reuse this source read-only. No second source corpus is needed.

New replay uses a private cold target and private diagnostics/output paths;
these are explicit relocations from the historical recipe, whose L186 replay
already changed paths successfully. No claim that cache/path identity is assumed.
One admitted scope, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
600s timeout per ELF, at most 6 build runs. Expected time: compilation and
mono/MIR/LLVM diagnostic emission. Stop on timeout/OOM, no cap increase.

`ELa_source_diff.json` records research HEAD `66fb62bbc803f67bbeb63a786620731379d5144f`:
zero changed crates/programs files, zero intervening commits touching those trees,
zero Cargo manifest/lock/config differences from the original compiler pin.
No FROZEN-IMPLEMENTATION source-drift finding exists on that comparison.

Expected deployed pins (SHA-256):
- default: f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet: 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool: 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Before/after theorem statements: unchanged; premise/recount delta 0. This stage
establishes provenance/availability, not security or joint non-vacuity.
#print axioms N/A. No contract/ledger edits, no push.
