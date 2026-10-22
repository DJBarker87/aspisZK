# Frozen ELF recheck — 21 October 2026

**PASS: default verifier MATCH; devnet verifier MATCH; Pool MATCH.**

This closes LOG D128's pending ELF identity check for the appended
`#[cfg(any(kani,aeneas_ref))]` `owned19` module in
`crates/aspis-r1-cost-probe/src/sim.rs`. The tested source is the complete
research tip `902ae095f2426798822c58107a773a4d5a6597d6`, branch
`codex/cx-elf-recheck-20261021`, including other changes since the original
freeze. No source was changed for this recheck.

| Program | Result | Bytes | Rebuilt and frozen SHA-256 | cmp exit |
|---|---|---:|---|---:|
| Default verifier | MATCH | 1,507,400 | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 0 |
| Devnet verifier | MATCH | 1,507,400 | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 0 |
| Pool | MATCH | 605,704 | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 0 |

All three unstripped `linked.elf` files also MATCH their corresponding pins in
`../freeze-20261020/artifacts-sha256.txt`. `comparisons.json` records all six
exact `cmp` commands, exit statuses, empty stdout/stderr and paired SHA-256
values. Each program receipt also contains literal `sha256sum` output for
both retained frozen files and rebuilt files.

The host was `dombarker@100.108.41.90` (`nuc`). Rebuilt artifacts remain under
`/home/dombarker/project-offloads/codex-cx-elf-recheck-20261021/artifacts/`;
comparisons used the retained original files under
`/home/dombarker/project-offloads/codex-cx-pin-20261020/artifacts/`.
No binaries or keys are committed.

## Exact build and resource evidence

| Target (release SBF) | Build exit | Wall seconds | Peak RSS KiB | Swaps | Cgroup memory peak bytes |
|---|---:|---:|---:|---:|---:|
| `programs/r1-cost-probe/Cargo.toml`, default IDs | 0 | 24.495 | 647,184 | 0 | 1,252,696,064 |
| `programs/r1-cost-probe/Cargo.toml`, devnet IDs | 0 | 2.252 | 203,036 | 0 | 142,651,392 |
| `programs/aspis-pool/Cargo.toml` | 0 | 23.763 | 644,628 | 0 | 973,975,552 |

Every row uses source revision `902ae095f2426798822c58107a773a4d5a6597d6`.
`#print axioms`: **N/A — no Lean jobs or theorem changes.** RSS and swaps are
GNU `/usr/bin/time -v` fields; cgroup memory peak is separately recorded and
includes the scope's aggregate accounting. These are artifact identity
results, not new formal security or runtime results.

Each build ran sequentially in its own named systemd user scope with
`MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, `TasksMax=64`.
The initial inventory showed no other user build scopes and approximately
54 GiB available on the 62 GiB host; this task reserved at most 8 GiB at once.
The host had pre-existing swap usage, but these scopes could not allocate
swap and all three timed builds recorded zero swaps. The live scope inventory,
limits and toolchain output are in `host-resources-and-toolchains.txt`.
No memory failure, cap increase, retry or SSH silence timeout occurred.

The freeze recipe was preserved: cargo-build-sbf 3.1.13, platform-tools v1.52,
SBF rustc 1.89.0-dev / LLVM 20.1.7; native Rust/Cargo 1.94.1; `--offline`,
`--locked`, `--skip-tools-install`, `-j 4`. Verifier features:
`pool-adapter,private-leaf-salts`. Pool features:
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`.
The default build unsets both deployment-ID variables; devnet uses the exact
frozen template copied in `harness/r1-devnet.template.json`.
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'` is set in the parent environment.
As in the freeze, cargo-build-sbf is invoked via `env -u RUSTFLAGS` with
`CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'`, because
SBF uses rust-lld directly. Per-target commands, environments, time reports,
complete build logs and limits are in `receipts/{default,devnet,pool}/`.

The isolated host workspace began as a reflink copy of the frozen workspace
and both compiled SBF caches. Current tracked crate/program/audit/xtask files,
Cargo inputs and tracked Rust sources/manifests elsewhere in the research
tree were overlaid from this worktree. There were no deleted build-source
paths between the freeze and this revision. All 8,213 transferred files were
SHA-256 checked against the local tree before building and again afterward;
`post-build-source-check.json` reports no changes. `source-hashes.json` includes
the workspace input subset and pins the full manifest retained on the host.
The cache was reused across default/devnet and separately for Pool; compiler
logs show optimized compilation at this source. No unchanged full regression
was run. `harness/rebuild.py` and `harness/capped.py` preserve the executed
build/comparison driver and resource receipt wrapper.

No assumptions were added or discharged by this check. The frozen executable
pins remain valid for this revision. D128's separate source-refinement and
privacy proof obligations are outside this ELF recheck and remain as recorded
in the research log.
