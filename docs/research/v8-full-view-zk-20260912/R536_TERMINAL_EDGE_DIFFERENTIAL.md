# R536 selected terminal-edge differential

This is focused runtime evidence for the selected R117 terminal calculation. It is not a proof of optimized-verifier acceptance, privacy, soundness, or end-to-end security.

## Final selected-flag target and environment

- Target: `docs/research/v8-full-view-zk-20260912/tools/r536_terminal_edge_check.rs`
- Target SHA-256: `551daf1f215ee6d1ef2e2a680c95bf684f88982b1d0066a95316e4e9c8d61c80`
- Selected-flag binary: `r117-terminal-edge-check`, SHA-256 `086c067565ce443db226563c02f404e3558f0b93045b7a864a7f70677e355dbb`
- Frozen selected R117 source revision: `6677`.
- Campaign HEAD: `0c5a3ecf8195eefc32fcd03431db4db2f3903be3`.
- Build host: pinned cached release workspace. Every build/run used `systemd-run --user --wait --collect --pipe`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.
- Selected environment: exact frozen `RUSTFLAGS` SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`; `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`; full value and verbose rustc invocation are in `raw/build8-selected-flags.env` and `raw/build8-selected-flags.log.gz`.
- Axioms: not applicable; this is a Rust runtime diagnostic.

The final selected-flag build (`raw/build8-selected-flags.log.gz`) exited 0 in 27.41 s with peak RSS 551,384 KiB and zero swap. The time was compilation after the explicit flag change, using the frozen performance-host target cache. Its matching selected-flag run (`raw/run8-selected-flags.log.gz`) exited 0 in 0.43 s with peak RSS 2,464 KiB and zero swap. It printed `R117_TERMINAL_COMPOSED_MATRIX_OK comparisons=630`.

`build7`/`run5` remain retained default-cfg results: their recorded `RUSTFLAGS` and `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS` are empty. They exited 0 (build 3.00 s, 249,976 KiB; run 0.53 s, 2,288 KiB; zero swap). They are not selected-host-flag evidence. See `evidence/r536-selected-terminal-edges/DEFAULT_CFG_630.md`.

## What the final run checked

The diagnostic ran 630 labelled cases: 3 `z` values, 5 alpha tuples, 3 beta values, two nonzero `(kappa,tau)` modes, and 7 final-256 vectors. The terminal vectors are units 0, 64, 128, 192, 127, and 255 plus one deterministic random vector. It uses fixed OOD-derived `abc`, `coin_weights_into(z, coins)`, nonzero rho, and the actual owned-primal fold.

For every case it checked:

- current R106 output equals the legacy scalar plus its sparse correction;
- current R106 plus image equals the dense source quotient dot;
- current query terminal equals dense query coefficients; and
- the composed terminal sums agree.

It also checks source original weights against the retained reference. The final selected-flag output ends `R117_TERMINAL_COMPOSED_MATRIX_OK comparisons=630`; the earlier default-cfg output is retained separately.

## Changed-diagnostic history

The package preserves every changed attempt. `build.log.gz` records the initial overlay workspace setup failure (cargo exit 101; 0.02 s; 19,180 KiB; zero swap; the wrapper status file incorrectly said 0 and is retained verbatim). `build2.log.gz` records the missing `structured_g` adapter import (exit 101; 25.25 s; 547,476 KiB; zero swap). `run.log.gz` records the first invalid dense-query transcription, which incorrectly multiplied query weights by query values. `run2.log.gz` records the next changed adapter before removal of the duplicate dense image addition. Their failure labels are preserved, but the first loop did not print a case label; `raw/CASE_ATTRIBUTION.md` withdraws any attribution to `e0` or the first case.

`run3.log.gz` is the one-case source localization after those corrections. `run4.log.gz` is the labelled zero-alpha terminal-coordinate check. Both pass. `run5.log.gz` is the final default-cfg matrix run. `run8-selected-flags.log.gz` is the final selected-flag matrix run. The corresponding final selected-flag build is `build8-selected-flags.log.gz`; both exit 0 with zero swap.

## Source and flag pins

`raw/source-imports-sha256.txt` enumerates 139 compiled Rust inputs. `raw/source-imports-vs-selected-r117.txt` records 138 byte-identical inputs relative to the frozen selected R117 root; the sole overlay-only file is this diagnostic. `raw/selected-host-flags.txt` records the release feature flags and bin stanza.

## Boundary and next obligation

No verifier source, security parameter, benchmark, or CU result changed. This runtime matrix does not cover every input, parser/error path, transcript/oracle chronology, shared-oracle law, or whole selected wrapper. The first remaining obligation is universal actual-wrapper equivalence, including errors and oracle chronology. See `raw/FULL_MATRIX_BOUNDARY.md` for the same scope statement.
