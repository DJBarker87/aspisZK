# Matching native extraction tools, 2026-10-16

Both native builds passed once. These are fresh, unpatched Linux builds of the translator and extractor revisions used by the accepted local extraction kits. No production, backend or generated Lean source changed; this bundle proves no new Rust/Lean correspondence theorem.

Host workspace: `/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016`.

- `bin/aeneas`: SHA-256 `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`; version `b59d5188c082f704a418c7cb4e52ad69328002d1`.
- `charon-target/release/charon`: SHA-256 `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`.
- Sibling `charon-driver`: SHA-256 `efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45`.

Charon is exact revision `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, reporting version `0.1.223` and toolchain `nightly-2026-06-01`. Put `/home/dombarker/.cargo/bin` in `PATH`; retain the sibling driver and pinned Rust toolchain. No `CHARON_TOOLCHAIN_IS_IN_PATH` override is needed. `tools-final-pins.json` records all resolved runtime libraries and their hashes.

The exact upstream archives and per-file hashes are inside `native-tools-evidence.tar.gz`. A post-build audit verified all 776 Aeneas and 1,166 Charon regular files unchanged. Local snapshot commits `220c7ff9...` and `d333b4ec...` contain those same regular source bytes and have clean tracked trees. Safe archive extraction normalized leading `./` in two documentation symlink targets; original and staged targets are recorded and normalize identically. The adjacent local Aeneas-workspace Charon checkout was not the matching snapshot. Neither the old `d860ac47` host translator nor the explicitly patched `b59...extended-static-return-r27` binary was selected.

## Build evidence and bounds

| Target | Exit | Wall seconds | Peak process RSS KiB | Observed cgroup peak bytes | Process swaps |
|---|---:|---:|---:|---:|---:|
| Charon and driver, release | 0 | 274.986 | 1,290,696 | 2,034,069,504 | 0 |
| Charon ML then Aeneas, release | 0 | 132.457 | 287,424 / 587,516 | 1,206,108,160 | 0 / 0 |

The two builds ran serially, each with actual `memory.high=6442450944`, `memory.max=8589934592`, `memory.swap.max=0`; no OOM/high/max events occurred. Charon used its own user systemd scope and `cargo +nightly-2026-06-01 build --release --locked --offline -j1 --bin charon --bin charon-driver`. The Linux dependency audit verifies 192 package entries against locked cached archives or clean pinned Git sources.

Aeneas used immutable dependency image `sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7` with network disabled, read-only root, one CPU, and an isolated writable workspace. The container entrypoint waited until the host verified and recorded the **container's actual cgroup** limits. Only then did its gate permit compilation. `build-aeneas.sh` built fresh exact Charon ML objects, asserted their library location, and built Aeneas with Dune release `-j1`. Logs record the selected library paths. No global opam state changed.

Receipt process-example keys are substring classifications: the first `ocamlopt` example is a hash command. Cap evidence comes from the gated container PID/cgroup, inherited process scope, captured build/link subprocesses and memory receipts, not that label alone. This is source identity and a bounded build claim, not cross-platform binary reproducibility.

## Retained artifacts

The archive contains source snapshots/pins, scripts, dependency metadata, environments, preflights, verbose logs, time reports, container inspections and final pins. `archive-members.json` hashes every regular member; `bundle-manifest.json` hashes the outer files. Native binaries remain at the host paths above. `preflight-corrections.json` explicitly records unsuccessful metadata/audit commands separately from green builds; their raw stderr was not saved as separate files. There was no Lean job, so an axioms audit is inapplicable. Extraction workers received these verified tools before evidence packaging.
