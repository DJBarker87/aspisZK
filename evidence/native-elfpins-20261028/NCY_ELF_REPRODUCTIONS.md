# NCY release ELF reproductions — 2026-10-28

Status: devnet reproduced; Pool pending; no release claim. Frozen source baseline
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Only NCY evidence changes.

The default verifier is reused from the fresh NCR_B003 reproduction:
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
1,563,728 bytes; exit 0, build wall 26.321091037 s, scoped wall 27.04 s,
peak process RSS 684392 KiB, cgroup peak 2438955008 bytes, swap 0.
See `../native-elfscope-20261028/NCR_SOURCE_TO_ELF.md` and its exact receipts.
That default artifact is not rebuilt by this lane.

## Recipe and evidence

NCY_SOURCE_PINS.json pins all frozen crates/programs and the prior Low2 build-input
census. Private source and warm SBF targets are COPIED from Low2, never modified
there; every selected local Rust source is touched only in the private copy so
Cargo recompiles it. Hash checks bracket each build. This is optimized release
SBF compilation/linking, not proof generation or a field arithmetic gate.

Pinned cargo-build-sbf 3.1.13, platform-tools v1.52, rustc 1.89.0-dev;
compiler SHA-256 `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002`;
cargo-build-sbf SHA-256 `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c`.
Exact commands/environment/source checks are in each stdout and host command JSON.
`--offline -j 4 -- --locked`, `CARGO_NET_OFFLINE=true`,
`CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4`.
No overflow/debug profile override or unrecorded RUSTFLAGS.

Devnet features: `pool-adapter,private-leaf-salts`.
Build-time Pool ID: `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`.
Build-time registry ID: `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`.
IDs are reused from Low2_build_manifest.json, not a live-cluster assertion.
Pool features: `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`;
verifier deployment-ID overrides are unset for Pool.

One scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64; admission needs exit 0 AND allowed:true before upload/launch.
NCY_ATTEMPTS.jsonl records actual revision, payload SHA, exit, wall, RSS, swaps
and exact scope command. No Lean theorem: #print axioms N/A. No Kani.

Own pre-launch repair NCY_P001: manifest in argv exceeded argument size;
transport changed to stdin with identical validation. No scope started for P001.
No shared launcher/reservation/shim/infrastructure was edited.

## Result table

| Target | Exit | Build wall s | Peak RSS KiB | Cgroup peak bytes | Swap peak bytes | Bytes | SHA-256 |
|---|---:|---:|---:|---:|---:|---:|---|
| devnet NCY_B001 | 0 | 28.453730122 | 686108 | 2506846208 | 0 | 1563728 | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 |

NCY_B001-time.log records full scoped wall 29.48 s; transport-included wall
29.698603584 s. The 1243 source/input pins match both before and after.

The compiler emits jobserver-FD/unused/deprecation warnings and stack-offset
`Error:` diagnostics for core/statement functions despite build exit 0 and
exact ELF identity. These diagnostics are retained in NCY_B001-stderr.log;
this is an artifact reproduction pass, not a stack-safety certification.
Reachability/stack safety of the final deployed path remains an S10 review
item; no source or tool setting was changed to suppress the diagnostics.

## Retained boundary

Matching ELF hashes establish exact artifact identity for this pinned recipe.
P7 SBF compiler/linker semantic preservation remains trusted. No live deployment
readback, loader-authority check, source/model bridge, syscall-value proof,
security experiment transport or final L188 audit is supplied by hash equality.
Keys, if generated, remain on the host at mode 0600; no key cleanup or refund.
No binaries, objects, keys or archives are committed.
