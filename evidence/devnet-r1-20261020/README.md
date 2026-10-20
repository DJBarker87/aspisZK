# R1 devnet resumption evidence

**Funded, blocked at release admission.** The payer holds 5 SOL. Default builds
reproduce the frozen pin, but env-configured IDs change `.text` because the
frozen ELF embeds its placeholder IDs as instruction immediates. The candidate
is **not** admitted as a data-only release. See [REPORT.md](REPORT.md) and
[artifacts-sha256.txt](artifacts-sha256.txt). No deployment or spend ran.

Source: `30eb0519a`, branch `codex/cx-devnet2-20261020`.
Host task root (reused, keys retained):
`dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
`keys/` is 0700, keys are 0600; never copy keys into the repository. No binaries
are committed. All utilities added here are Rust or shell orchestration.

The [public config](../../config/r1-devnet.template.json) retains the reserved
identities and original frozen artifact paths. Its `devnet_build_candidate`
field identifies the rejected candidate separately; it does not promote it.
Mint is still null. There is **no end-to-end RPC spend driver** in this result.
Raw proof/statement account carrier setup remains open. The admitted verifier
still rejects legacy lifecycle tags 4/5/6.

## Build commands executed

The host `src/` and SBF/native caches were copied into this task's own directory
from the pinned adoption workspace, then the assigned worktree's changed
sources and current crate manifest were copied over. No shared source or cache
was rewritten. Before launch, inspect populated cgroup reservations; sum of
`MemoryMax` including the next scope must stay below 55 GiB. Builds expect
incremental optimized compilation, not proof generation.

Final commands, on the host (receipt directories must not already exist;
the script refuses overwrites). Do not rerun unchanged builds unnecessarily:

```sh
cd /home/dombarker/project-offloads/codex-cx-devnet-20261020
task=$PWD
systemd-run --user --scope \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_build.sh "$task" default 30eb0519a
systemd-run --user --scope \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_build.sh "$task" devnet 30eb0519a
```

The script reads `.programs.pool` and `.programs.registry` from
`r1-devnet.template.json`, exporting `ASPIS_R1_POOL_PROGRAM_ID` and
`ASPIS_R1_REGISTRY_PROGRAM_ID` for the devnet build only. Both use
`pool-adapter,private-leaf-salts`, SBF 3.1.13/platform-tools v1.52,
`--offline --locked -j 4`. Default unsets both env variables.
`option_env!` tracks environment changes for recompilation. Invalid or
non-canonical 32-byte base58 values fail const evaluation.

Native jobs use `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. SBF's direct
`rust-lld` rejects that cc-driver spelling, so the build script removes it
for SBF and sets the equivalent target flag
`CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'`.
All three affected linker/build-script failed or rejected attempts have
retained receipts; see REPORT for the replacement.

## Identity gate commands executed

```sh
frozen=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/verifier/aspis_r1_cost_probe_program.so
obj=$HOME/.cache/solana/v1.52/platform-tools/llvm/bin
sha256sum "$frozen" artifacts/default/aspis_r1_cost_probe_program.so \
  artifacts/devnet/aspis_r1_cost_probe_program.so
cmp "$frozen" artifacts/default/aspis_r1_cost_probe_program.so
"$obj/llvm-objdump" -h "$frozen"
"$obj/llvm-objdump" -h artifacts/devnet/aspis_r1_cost_probe_program.so
"$obj/llvm-objcopy" --dump-section .text=frozen.text "$frozen"
"$obj/llvm-objcopy" --dump-section .text=devnet.text artifacts/devnet/aspis_r1_cost_probe_program.so
cmp frozen.text devnet.text
"$obj/llvm-objdump" -d "$frozen"
```

Default `cmp` returns 0. Devnet text `cmp` returns 1. Do not treat a successful
compiler exit as release admission. The independent Rust auditor checks section
layout, `.text`, exact data substitutions, and all remaining file bytes:

```sh
systemd-run --user --scope \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /home/dombarker/.cargo/bin/rustc --edition=2021 -O \
  -C link-arg=-Wl,--threads=4 src/scripts/r1_deployment_elf_check.rs -o elf-check
./elf-check "$frozen" artifacts/devnet/aspis_r1_cost_probe_program.so \
  BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs \
  9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
```

The auditor **must return 1** for the current candidate. Final receipts are
under `receipts/final-native-checks/audit.*`. The audit itself used the same
capped scope as its compilation and the native tests. Native test command:

```sh
cd src
RUSTFLAGS='-C link-arg=-Wl,--threads=4' \
CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-cx-devnet-20261020/native-target \
  cargo test --release --offline --locked -j 4 \
  -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts --lib
```

Run that command only inside the capped scope above; final result: **34 passed**.

## Bounded funding watcher

The executed watcher verified devnet genesis, called finalized `getBalance`
every five minutes, and retried public `requestAirdrop` once per hour. It
stops at >=3 SOL or after eight hours, preserving every request and response.
It observed 0 SOL at 07:43:58 UTC, faucet 429, then 5 SOL at 07:48:58 UTC,
and exited 0. It is no longer running. `signatures.json` links the finalized
incoming funding transfer; it was submitted externally.

For a genuinely needed new funding watch, use a new unit and receipt name:

```sh
task=/home/dombarker/project-offloads/codex-cx-devnet-20261020
systemd-run --user --unit=cx-devnet2-funding-N \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /bin/bash "$task/r1_devnet_funding_watch.sh" \
  "$task/r1-devnet.template.json" "$task/receipts/funding-watch-N"
```

The 3-SOL trigger is not sufficient deployment funding: measured programdata
rent for the candidate plus Pool and registry is **11.284747560 SOL**, before
other accounts, fees, setup and temporary buffer requirements. Keep all keys.
No refund or cleanup has been attempted.

## What remains

The lead decision must account for instruction-embedded IDs and admit an
appropriate new `.text` pin and validations. Then sufficient funding, three
program deployments, registry/master/lanes/pages/vault/mint setup, spendable
note deposit, P_R1 retrying proof generation, carrier uploads, verifier
checkpoint, transfer/withdrawal, both negative checks, and a complete RPC
driver remain. No deploy command or placeholder driver is presented as ready
while the required identity gate is false. Per-phase CU/wall data for those
stages remains unmeasured, with zero uploads and worker submissions.
